module

public import VerifiedGarbage.Impl.Gcm.X86_64.Flag
meta import VerifiedGarbage.Impl.Gcm.X86_64.Flag
public import VerifiedGarbage.Proof.AesGcm.Flag
meta import VerifiedGarbage.Proof.AesGcm.Flag
import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Block
meta import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareAvx
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareZ
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Spec.Gcm.Prepared16
public import VerifiedGarbage.Impl.Gcm.X86_64.Prepare16
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Zeroize.Common
public import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
meta import VerifiedGarbage.Impl.Gcm.X86_64.PrepareAvx
meta import VerifiedGarbage.Impl.Gcm.X86_64.PrepareZ
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Spec.Gcm.Prepared
meta import VerifiedGarbage.Spec.Gcm.Prepared16
meta import VerifiedGarbage.Impl.Gcm.X86_64.Prepare16
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Zeroize.Common
meta import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch

/-!
# Preparing a key context's powers in place: the contract on the registers

`prepareX86_64`, `vg_aes_gcm_prepare`'s contract on the registers; the
constant time of its implementation (`prepareZ_ct`): only the context's
address affects timing; and `verified_of`, which proves `Verified` for any
code that writes the prepared powers and nothing else (`PrepOk`); likewise
for `vg_aes_gcm_prepare16` (`prepare16X86_64`, `verified_ofW`). The field,
where each implementation's powers are proven, is in `Stitch/Ok.lean`,
`PrepareAvx/Ok.lean` and `PrepareZ.lean`, so that its algebra reaches no new
module.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Prepare

open VG VG.X86_64

/-- `vg_aes_gcm_prepare`'s contract, on the registers. -/
def prepareX86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1024⟩] ∧ (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    Spec.Gcm.PreparedPowersRepr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

theorem prepareZ_ct :
    ConstantTime isa prepareX86_64.pre prepareX86_64.pub Impl.Gcm.X86_64.PrepareZ.prepare := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

/-- What code computing the first `p` pairs of prepared powers does from `s₀`:
those powers of the hash subkey at `C + 240` into pairs 0 to `p - 1` of the
context at `C`, nothing written outside its bytes 256–1023, and the
registers but `rax` and `r11` kept. -/
def PrepOkN (p : Nat) (s₀ s : State) : Prop :=
  (∀ k < p, ∀ l < 2, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (2 * k + 2 - l))) ∧
  Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩] s₀.mem s.mem ∧
  (∀ r, r ≠ .rax → r ≠ .r11 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

/-- What `vg_aes_gcm_prepare` does from `s₀`: all 48 prepared powers. -/
def PrepOk (s₀ s : State) : Prop := PrepOkN 24 s₀ s

theorem bytesAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt m' p n = Spec.Aes.bytesAt m p n := by
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem correct {c : Prog isa}
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 → WP isa c s₀ (PrepOk s₀))
    {s₀ : State} (hp : prepareX86_64.pre s₀) :
    WP isa c s₀ fun s => gprPreserved s₀ s ∧ prepareX86_64.post s₀ s := by
  obtain ⟨_, hwr, hwrap, hret⟩ := hp
  have hw : InRegions s₀.wr (s₀.gpr .rdi) 1024 := by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (hok s₀ hw hwrap) fun s ⟨pw, fr, g, _, _⟩ => ?_
  have keep : Spec.Aes.bytesAt s.mem (s₀.gpr .rdi) 256 = Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) 256 :=
    bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  have hH : Spec.Gcm.ctxH s.mem (s₀.gpr .rdi) = Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi) := by
    simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
    rw [bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (Offset.disjoint (s₀.gpr .rdi) (d := 240) (n := 16) (e := 256) (k := 768) (.inl (by decide)) (by decide)
        (by omega)).sub_left (Region.sub_prefix (Nat.le_refl _))) (by decide)]
  refine ⟨⟨fun r hr => by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide), ?_⟩, keep,
    fun k hk => ?_⟩
  · exact fr.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) (by decide))) (by decide)
  · rw [hH]
    have p0 := pw k hk 0 (by decide)
    have p1 := pw k hk 1 (by decide)
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
    rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
    exact ⟨p0, p1⟩

theorem prepare_correct {c : Prog isa}
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 → WP isa c s₀ (PrepOk s₀))
    (hx : c.allInstrs (fun i => !loadsMxcsr i) = true) (s : State) (hs : prepareX86_64.pre s) :
    ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ prepareX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := correct hok hs
  exact ⟨t, s', he, abiPreserved_of_exec hx he h.1, h.2⟩

/-- A state meeting `prepareContract`'s precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1024⟩]

/-- `Verified` for code that writes the prepared powers and nothing else,
loads no MXCSR, and is constant time. -/
theorem verified_of (c : Prog isa)
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 → WP isa c s₀ (PrepOk s₀))
    (hx : c.allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa prepareX86_64.pre prepareX86_64.pub c) :
    Verified X86_64.target c (Spec.Gcm.prepareContract X86_64.abi) :=
  Verified.of_correct (prepare_correct hok hx) hct (by
    sig_implies [Spec.Gcm.prepareContract, Spec.Gcm.prepareSig, Spec.Gcm.preparePost, prepareX86_64,
      X86_64.abi, X86_64.argRegs] [satState] using satState)

end VG.Proof.Gcm.X86_64.Prepare

/-! `vg_aes_gcm_prepare16`: its contract on the registers and constant time;
its powers are proven in `Stitch/Ok.lean`. -/

namespace VG.Proof.Gcm.X86_64.Prepare16

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Prepare16 (prepare16)

/-- `vg_aes_gcm_prepare16`'s contract, on the registers. -/
def prepare16X86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1024⟩] ∧ (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    Spec.Gcm.PreparedPowers16Repr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

theorem prepare16_ct : ConstantTime isa prepare16X86_64.pre prepare16X86_64.pub prepare16 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

/-- `vg_aes_gcm_prepare` on 256-bit registers, under `prepareContract`'s
register contract. -/
theorem prepare_ct : ConstantTime isa VG.Proof.Gcm.X86_64.Prepare.prepareX86_64.pre
    VG.Proof.Gcm.X86_64.Prepare.prepareX86_64.pub Impl.Gcm.X86_64.Prepare16.prepare := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

/-- `vg_aes_gcm_prepare` on 128-bit registers, under `prepareContract`'s
register contract. -/
theorem prepareAvx_ct : ConstantTime isa VG.Proof.Gcm.X86_64.Prepare.prepareX86_64.pre
    VG.Proof.Gcm.X86_64.Prepare.prepareX86_64.pub Impl.Gcm.X86_64.PrepareAvx.prepare := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

/-- `vg_aes_gcm_prepare` on SSE registers, under `prepareContract`'s register
contract. -/
theorem prepareSse_ct : ConstantTime isa VG.Proof.Gcm.X86_64.Prepare.prepareX86_64.pre
    VG.Proof.Gcm.X86_64.Prepare.prepareX86_64.pub Impl.Gcm.X86_64.PrepareAvx.prepareSse := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem prepare16Avx_ct :
    ConstantTime isa prepare16X86_64.pre prepare16X86_64.pub Impl.Gcm.X86_64.PrepareAvx.prepare16 := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

open VG.Proof.Gcm.X86_64.Prepare (bytesAt_frame satState)

/-- What an implementation of `vg_aes_gcm_prepare16` may do from `s₀`: the 16
prepared powers of the hash subkey at `C + 240` into pairs 0–7 of the
context at `C`, nothing written but bytes 256–1023 of the context, and the
registers but `rax` kept. -/
def PrepOk16W (s₀ s : State) : Prop :=
  (∀ k < 8, ∀ l < 2, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (2 * k + 2 - l))) ∧
  Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩] s₀.mem s.mem ∧
  (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr

theorem correctW {c : Prog isa}
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 →
      WP isa c s₀ (PrepOk16W s₀))
    {s₀ : State} (hp : prepare16X86_64.pre s₀) :
    WP isa c s₀ fun s => gprPreserved s₀ s ∧ prepare16X86_64.post s₀ s := by
  obtain ⟨_, hwr, hwrap, hret⟩ := hp
  have hw : InRegions s₀.wr (s₀.gpr .rdi) 1024 := by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  refine WP.mono (hok s₀ hw hwrap) fun s ⟨pw, fr, g, _, _⟩ => ?_
  have keep : Spec.Aes.bytesAt s.mem (s₀.gpr .rdi) 256 = Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) 256 :=
    bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  have hH : Spec.Gcm.ctxH s.mem (s₀.gpr .rdi) = Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi) := by
    simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
    rw [bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact (Offset.disjoint (s₀.gpr .rdi) (d := 240) (n := 16) (e := 256) (k := 768) (.inl (by decide)) (by decide)
        (by omega)).sub_left (Region.sub_prefix (Nat.le_refl _))) (by decide)]
  refine ⟨⟨fun r hr => g r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩, keep, fun k hk => ?_⟩
  · exact fr.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) (by decide))) (by decide)
  · rw [hH]
    have p0 := pw k hk 0 (by decide)
    have p1 := pw k hk 1 (by decide)
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
    rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
    exact ⟨p0, p1⟩

/-- `Verified` for code that writes the first 16 prepared powers and nothing
outside bytes 256–1023 of the context, loads no MXCSR, and is constant
time. -/
theorem verified_ofW (c : Prog isa)
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 →
      WP isa c s₀ (PrepOk16W s₀))
    (hx : c.allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa prepare16X86_64.pre prepare16X86_64.pub c) :
    Verified X86_64.target c (Spec.Gcm.prepare16Contract X86_64.abi) :=
  Verified.of_correct (fun s hs => by
      obtain ⟨t, s', he, h⟩ := correctW hok hs
      exact ⟨t, s', he, abiPreserved_of_exec hx he h.1, h.2⟩) hct (by
    sig_implies [Spec.Gcm.prepare16Contract, Spec.Gcm.prepareSig, Spec.Gcm.prepare16Post, prepare16X86_64,
      X86_64.abi, X86_64.argRegs] [satState] using satState)


theorem implies16 : prepare16X86_64.Implies (Spec.Gcm.prepare16Contract X86_64.abi) := by
  sig_implies [Spec.Gcm.prepare16Contract, Spec.Gcm.prepareSig, Spec.Gcm.prepare16Post, prepare16X86_64,
    X86_64.abi, X86_64.argRegs] [satState] using satState

/-- A run that writes nothing of the context but its bytes 256–511 (the 16
powers) writes none of `ctx` from byte 512 on (`Artifact.written`), so a
caller wipes only its first 512 bytes. -/
theorem written16 {c : Prog isa}
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 →
      WP isa c s₀ fun s => Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 256⟩] s₀.mem s.mem)
    (s : State) (t : List Leak) (s' : State) (hs : (Spec.Gcm.prepare16Contract X86_64.abi).pre s)
    (he : Exec isa c s t s') :
    Sig.writtenWithin (X86_64.abi.withConsts []) Spec.Gcm.prepareSig [("ctx", 512)] s s' := by
  obtain ⟨_, hwr, hwrap, _⟩ := implies16.pre s hs
  have hw : InRegions s.wr (s.gpr .rdi) 1024 := by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩
  obtain ⟨t', s'', he', hf⟩ := hok s hw hwrap
  obtain ⟨-, rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin, X86_64.abi, X86_64.argRegs, Abi.withConsts, Spec.Gcm.prepareSig,
    Sig.words, Sig.arrays, Param.words, ArgWord.bits]
  intro i h1 h2
  have h2' : i < 1024 := by simpa [Elem.size] using h2
  refine hf _ fun r hr hc => ?_
  rw [List.mem_singleton] at hr
  subst hr
  exact Offset.disjoint (s.gpr .rdi) (d := i) (n := 1) (e := 256) (k := 256) (.inr (by omega)) (by omega)
    (by omega) _ (Region.contains_self _ _) hc

end VG.Proof.Gcm.X86_64.Prepare16

/-! `vg_aes_gcm_prepare` on the 1032-byte prepared key context, whose word at
byte 1024 counts the powers present (`Proof.AesGcm.Flag.PreparedRepr`): the code that
computes none and sets it to 0 (`prepareAbsent`), and each implementation
that computes 48 or 16, after setting it to their number
(`prepareFlagged`). -/

namespace VG.Proof.Gcm.X86_64.Prepare

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Flag (storeFlag prepareAbsent prepareFlagged)

/-- `vg_aes_gcm_prepare`'s contract on the prepared key context, on the
registers. -/
def flaggedX86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1032⟩] ∧ (s.gpr .rdi).toNat + 1032 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1032⟩
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    Proof.AesGcm.Flag.PreparedRepr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

/-- A state meeting the flagged `prepareContract`'s precondition. -/
def flaggedSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1032⟩]

theorem flagged_implies : flaggedX86_64.Implies (Proof.AesGcm.Flag.prepareContract X86_64.abi) := by
  sig_implies [Proof.AesGcm.Flag.prepareContract, Proof.AesGcm.Flag.prepareSig, Proof.AesGcm.Flag.preparePost,
    flaggedX86_64, X86_64.abi, X86_64.argRegs] [flaggedSat] using flaggedSat

/-- `storeFlag v` from `s₀`: the count is `v`, and only it and `rax`
changed. -/
theorem storeFlag_run (v : BitVec 32) (s₀ : State)
    (hw : InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 1024) 8) :
    WP isa (.block (storeFlag v)) s₀ fun s =>
      s.mem = s₀.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 1024) (v.signExtend 64) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have ho : BitVec.ofInt 64 ((1024 : Nat) : Int) = BitVec.ofNat 64 1024 := rfl
  refine WP.of_runBlock ⟨{ s₀.setReg .rax (v.signExtend 64) with
    mem := s₀.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 1024) (v.signExtend 64) }, ?_, ?_⟩
  · simp only [storeFlag, Impl.Gcm.X86_64.Flag.flagOff, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, Option.map_some, State.store64, State.ea, ho, RegUpd.wr_setReg, hw, ↓reduceIte,
      RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (show ¬Reg.rdi = .rax by decide)]
    rfl
  · exact ⟨rfl, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩

theorem flagged_pre {s₀ : State} (hp : flaggedX86_64.pre s₀) :
    InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 1024) 8 := by
  rw [hp.2.1]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by decide) (by decide)⟩

/-- The calling convention after `storeFlag` and then code that writes only
`regions`, inside the context. -/
theorem flagged_gpr {s₀ s₁ s : State} {v : BitVec 64} (hp : flaggedX86_64.pre s₀)
    (hm₁ : s₁.mem = s₀.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 1024) (v : BitVec 64))
    (hg₁ : ∀ r, r ≠ .rax → s₁.gpr r = s₀.gpr r)
    {d k : Nat} (hdk : d + k ≤ 1032) (fr : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 d, k⟩] s₁.mem s.mem)
    (hg : ∀ r, r ≠ .rax → r ≠ .r11 → s.gpr r = s₁.gpr r) : gprPreserved s₀ s := by
  obtain ⟨_, _, _, hret⟩ := hp
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact (hg _ (by decide) (by decide)).trans (hg₁ _ (by decide))
  · have fr₀ : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 1024, 8⟩] s₀.mem s₁.mem := by
      rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    rw [fr.readW (Region.contains_self _ _) (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) hdk)) (by decide)]
    exact fr₀.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) (by decide))) (by decide)

theorem absent_ct :
    ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub prepareAbsent := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem absent_correct (s₀ : State) (hp : flaggedX86_64.pre s₀) :
    ∃ t s', Exec isa prepareAbsent s₀ t s' ∧ abiPreserved s₀ s' ∧ flaggedX86_64.post s₀ s' := by
  obtain ⟨t, s', he, hm, hg, _, _⟩ := storeFlag_run 0 s₀ (flagged_pre hp)
  have fr : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 1024, 8⟩] s₀.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨t, s', he, abiPreserved_of_exec (by rfl) he
    (flagged_gpr hp hm hg (d := 1024) (k := 8) (by decide) (Frame.refl _ _) fun _ _ _ => rfl), ?_, ?_⟩
  · exact bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  · have hc : Proof.AesGcm.Flag.powerCount s'.mem (s₀.gpr .rdi) = 0 := by
      simp only [Proof.AesGcm.Flag.powerCount]
      rw [show (s₀.gpr .rdi + 1024 : Addr) = s₀.gpr .rdi + BitVec.ofNat 64 1024 from rfl, hm,
        Mem.readW_writeW_self64]
      rfl
    exact ⟨fun h => absurd (hc ▸ h) (by decide), fun h => absurd (hc ▸ h) (by decide)⟩

/-- `vg_aes_gcm_prepare` computing no powers. -/
theorem absent_verified : Verified X86_64.target prepareAbsent (Proof.AesGcm.Flag.prepareContract X86_64.abi) :=
  Verified.of_correct absent_correct absent_ct flagged_implies

/-- `prepareFlagged n c`, for code `c` that writes the first `n` prepared
powers, 16 or 48, and nothing else (`PrepOkN`). -/
theorem flagged_correct {n : Nat} (hn : n = 16 ∨ n = 48) {c : Prog isa}
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 →
      WP isa c s₀ (PrepOkN (n / 2) s₀))
    (hx : c.allInstrs (fun i => !loadsMxcsr i) = true) (s₀ : State) (hp : flaggedX86_64.pre s₀) :
    ∃ t s', Exec isa (prepareFlagged n c) s₀ t s' ∧ abiPreserved s₀ s' ∧ flaggedX86_64.post s₀ s' := by
  have hx' : (prepareFlagged n c).allInstrs (fun i => !loadsMxcsr i) = true := by
    simp only [prepareFlagged, Code.allInstrs, hx, Bool.and_true]; rfl
  have hwrap := hp.2.2.1
  have hwr := hp.2.1
  have hW : WP isa (prepareFlagged n c) s₀ fun s => gprPreserved s₀ s ∧ flaggedX86_64.post s₀ s := by
    rw [prepareFlagged, WP.seq_iff]
    refine WP.mono (storeFlag_run (BitVec.ofNat 32 n) s₀ (flagged_pre hp)) fun s₁ ⟨hm₁, hg₁, _, hwr₁⟩ => ?_
    have hrdi : s₁.gpr .rdi = s₀.gpr .rdi := hg₁ _ (by decide)
    have hw : InRegions s₁.wr (s₁.gpr .rdi) 1024 := by
      rw [hwr₁, hrdi, hwr]
      exact ⟨_, List.mem_singleton_self _, by
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
    refine WP.mono (hok s₁ hw (by rw [hrdi]; omega)) fun s ⟨pw, fr, g, _, _⟩ => ?_
    rw [hrdi] at pw fr
    have fr₀ : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 1024, 8⟩] s₀.mem s₁.mem := by
      rw [hm₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have keep₁ : Spec.Aes.bytesAt s₁.mem (s₀.gpr .rdi) 256 = Spec.Aes.bytesAt s₀.mem (s₀.gpr .rdi) 256 :=
      bytesAt_frame fr₀ (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
    have keep : Spec.Aes.bytesAt s.mem (s₀.gpr .rdi) 256 = Spec.Aes.bytesAt s₁.mem (s₀.gpr .rdi) 256 :=
      bytesAt_frame fr (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
    have hH : Spec.Gcm.ctxH s.mem (s₀.gpr .rdi) = Spec.Gcm.ctxH s₁.mem (s₀.gpr .rdi) := by
      simp only [Spec.Gcm.ctxH, Spec.Gcm.blockAt]
      rw [bytesAt_frame fr (fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact (Offset.disjoint (s₀.gpr .rdi) (d := 240) (n := 16) (e := 256) (k := 768) (.inl (by decide))
          (by decide) (by omega)).sub_left (Region.sub_prefix (Nat.le_refl _))) (by decide)]
    have hc : Proof.AesGcm.Flag.powerCount s.mem (s₀.gpr .rdi) = n := by
      simp only [Proof.AesGcm.Flag.powerCount]
      rw [show (s₀.gpr .rdi + 1024 : Addr) = s₀.gpr .rdi + BitVec.ofNat 64 1024 from rfl,
        fr.readW (r := ⟨s₀.gpr .rdi + BitVec.ofNat 64 1024, 8⟩) (Region.contains_self _ _) (fun r hr => by
          obtain rfl := List.mem_singleton.mp hr
          exact Offset.disjoint (s₀.gpr .rdi) (d := 1024) (n := 8) (e := 256) (k := 768) (.inr (by decide))
            (by decide) (by omega)) (by decide), hm₁, Mem.readW_writeW_self64]
      rcases hn with rfl | rfl <;> rfl
    have pairs (q : Nat) (hq : q ≤ n / 2) : ∀ k < q,
        s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k)) 128 =
          Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (s₀.gpr .rdi)) (2 * k + 2)) ∧
        s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (272 + 32 * k)) 128 =
          Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s.mem (s₀.gpr .rdi)) (2 * k + 1)) := by
      intro k hk
      rw [hH]
      have p0 := pw k (by omega) 0 (by decide)
      have p1 := pw k (by omega) 1 (by decide)
      rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
      rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
      exact ⟨p0, p1⟩
    refine ⟨flagged_gpr hp hm₁ hg₁ (by decide) fr g, keep.trans keep₁, fun h => pairs 8 ?_, fun h => pairs 24 ?_⟩
    · rw [hc] at h; omega
    · rw [hc] at h; omega
  obtain ⟨t, s', he, hg, hpost⟩ := hW
  exact ⟨t, s', he, abiPreserved_of_exec hx' he hg, hpost⟩

/-- `Verified` for `prepareFlagged n c`, for code `c` that writes the first
`n` prepared powers, 16 or 48, and nothing else, loads no MXCSR, and is
constant time. -/
theorem flagged_verified {n : Nat} (hn : n = 16 ∨ n = 48) (c : Prog isa)
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 →
      WP isa c s₀ (PrepOkN (n / 2) s₀))
    (hx : c.allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged n c)) :
    Verified X86_64.target (prepareFlagged n c) (Proof.AesGcm.Flag.prepareContract X86_64.abi) :=
  Verified.of_correct (flagged_correct hn hok hx) hct flagged_implies

/-- The constant time of each implementation that computes the powers, after
`storeFlag`. -/
theorem flaggedZ_ct :
    ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged 48 Impl.Gcm.X86_64.PrepareZ.prepare) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem flagged16_ct :
    ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged 16 Impl.Gcm.X86_64.Prepare16.prepare16) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem flaggedAvx_ct :
    ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged 16 Impl.Gcm.X86_64.PrepareAvx.prepare16) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

/-! `vg_aes_gcm_wipe_prepared` (`wipe avx`): `onFlag 48` and `onFlag 16`
choose among three blocks that zero the context from a zero vector register,
32 bytes at a time from `ymm0` with AVX and 16 from `xmm0` without: the first
1024 bytes where the count is at least 48, 512 where it is at least 16, and
256 where it is less. Each block is verified against `wipePreparedContract`
with the count's range in its precondition and no leak (`wipeBranch`), and
`Verified.of_onFlagCtx` joins them: the inner choice leaks `flagLeak`, the
outer `flagLeak` again, which the contract's one `flagLeak` gives
(`Verified.leak_mono`). -/

open VG.Impl.Gcm.X86_64.Flag (storeBytes zeroStore zeroStores zeroReg zeroBlocks wipe)
open VG.Proof.Zeroize (Prefix prefix_writeW prefix_spec)

/-- The register `zeroStore avx` stores from is zero. -/
def Src0 (avx : Bool) (s : State) : Prop := if avx then s.ymm .xmm0 = 0 else s.xmm .xmm0 = 0

/-- What `zeroStores avx k n` keeps and makes, from `s`. -/
def ZOk (s : State) (i : Nat) (t : State) : Prop :=
  t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.xmm = s.xmm ∧ t.ymmHi = s.ymmHi ∧ t.mxcsr = s.mxcsr ∧
  Prefix t.mem (s.gpr .rdi) i ∧ Frame s.wr s.mem t.mem

theorem ofInt_nat (d : Nat) : BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d := BitVec.ofInt_natCast _ _

theorem zeroStore_run (avx : Bool) (s : State) (d : Nat) (hx : Src0 avx s)
    (hs : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 d) (storeBytes avx)) :
    isa.exec (zeroStore avx d) s =
      some { s with mem := s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 d) (0 : BitVec (8 * storeBytes avx)) } := by
  cases avx <;> simp only [Src0, storeBytes, Bool.false_eq_true, ↓reduceIte] at hx hs <;>
    simp only [zeroStore, Bool.false_eq_true, ↓reduceIte, exec, State.store128, State.store256, State.ea,
      ofInt_nat, hx, hs] <;> rfl

theorem zeroStores_ok (avx : Bool) (n : Nat) : ∀ (k : Nat) (s₀ s : State),
    Src0 avx s → storeBytes avx * (k + n) < 2 ^ 64 →
    (∀ j < n, InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 (storeBytes avx * (k + j))) (storeBytes avx)) →
    ZOk s₀ (storeBytes avx * k) s →
    WP isa (.block (zeroStores avx k n)) s (ZOk s₀ (storeBytes avx * (k + n))) := by
  have hb : 8 * storeBytes avx / 8 = storeBytes avx := by omega
  induction n with
  | zero => intro k s₀ s _ _ _ h; exact WP.block_nil (by simpa using h)
  | succ n ih =>
    intro k s₀ s hx hn hw h
    obtain ⟨hg, hrd, hwr, hxm, hyh, hmx, hz, hf⟩ := h
    have hs := hw 0 (by omega)
    rw [Nat.add_zero] at hs
    have hd : s.gpr .rdi = s₀.gpr .rdi := by rw [hg]
    let s' : State :=
      { s with mem := s.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 (storeBytes avx * k)) (0 : BitVec (8 * storeBytes avx)) }
    rw [show k + (n + 1) = k + 1 + n by omega] at hn ⊢
    have hle : storeBytes avx * (k + 1) ≤ storeBytes avx * (k + 1 + n) := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at hle
    refine WP.block_cons_iff.mpr ⟨s', ?_, ih (k + 1) s₀ s' hx hn
      (fun j hj => by
        have := hw (j + 1) (by omega); rwa [show k + (j + 1) = k + 1 + j by omega] at this) ?_⟩
    · have := zeroStore_run avx s (storeBytes avx * k) hx (by rw [hd, hwr]; exact hs)
      rw [hd] at this
      exact this
    · obtain ⟨r, hr, hc⟩ := hs
      have hp := prefix_writeW (w := 8 * storeBytes avx) hz (by rw [hb]; omega)
      rw [hb, ← Nat.mul_succ] at hp
      exact ⟨hg, hrd, hwr, hxm, hyh, hmx, hp, hf.writeW hr _ (by rw [hb]; exact hc)⟩


/-- The zeroing of the register the stores read: `pxor` without AVX,
`vpxor` with. -/
theorem zero_run (avx : Bool) (s : State) : ∃ s₁, isa.exec (zeroReg avx) s = some s₁ ∧
    Src0 avx s₁ ∧ s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧ s₁.mxcsr = s.mxcsr := by
  cases avx <;> refine ⟨_, rfl, ?_⟩ <;> simp [Src0, XOp.exec, VOp.exec, State.setXmm, State.setV, State.ymm, State.lane,
    XBinOp.eval, VBinOp.sse]

/-- `zeroBlocks avx (storeBytes avx * n)` from `s₀`: the first
`storeBytes avx * n` bytes at `rdi` are zero, and nothing else the calling
convention or the contract reads changed. -/
theorem zeroBlocks_ok (avx : Bool) (n : Nat) (s₀ : State) (hn : storeBytes avx * n < 2 ^ 64)
    (hw : ∀ j < n, InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 (storeBytes avx * j)) (storeBytes avx)) :
    WP isa (.block (zeroBlocks avx (storeBytes avx * n))) s₀ fun t =>
      t.gpr = s₀.gpr ∧ t.mxcsr = s₀.mxcsr ∧ Prefix t.mem (s₀.gpr .rdi) (storeBytes avx * n) ∧
        Frame s₀.wr s₀.mem t.mem := by
  obtain ⟨s₁, he, hx, hg, hm, hrd, hwr, hmx⟩ := zero_run avx s₀
  have h0 : ZOk s₁ (storeBytes avx * 0) s₁ :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun j hj => absurd hj (by omega), Frame.refl _ _⟩
  have hst := zeroStores_ok avx n 0 s₁ s₁ hx (by rw [Nat.zero_add]; exact hn)
    (fun j hj => by rw [hg, hwr, Nat.zero_add]; exact hw j hj) h0
  have fin (t : State) (h : ZOk s₁ (storeBytes avx * (0 + n)) t) :
      t.gpr = s₀.gpr ∧ t.mxcsr = s₀.mxcsr ∧ Prefix t.mem (s₀.gpr .rdi) (storeBytes avx * n) ∧
        Frame s₀.wr s₀.mem t.mem := by
    obtain ⟨tg, _, _, _, _, tmx, tz, tf⟩ := h
    rw [hg, Nat.zero_add] at tz
    rw [hwr, hm] at tf
    exact ⟨tg.trans hg, tmx.trans hmx, tz, tf⟩
  have e : storeBytes avx * n / storeBytes avx = n := by cases avx <;> simp [storeBytes]
  simp only [zeroBlocks, e, List.cons_append]
  refine WP.block_cons_iff.mpr ⟨s₁, he, WP.block_append_iff.mpr (WP.mono hst fun t h => ?_)⟩
  cases avx
  · exact WP.block_nil (fin t h)
  · exact WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil (fin t h)⟩


/-- `wipe`'s contract on the registers, for the block that runs where the
count satisfies `F`. -/
def wipeX86_64 (F : Nat → Prop) : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1032⟩] ∧ (s.gpr .rdi).toNat + 1032 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1032⟩ ∧ F (s.mem.readW (s.gpr .rdi + 1024) 64).toNat
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) (Proof.AesGcm.Flag.wipePreparedLen s.mem (s.gpr .rdi)) =
    List.replicate (Proof.AesGcm.Flag.wipePreparedLen s.mem (s.gpr .rdi)) 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

/-- The block of `wipe avx` zeroing `bytes` bytes, where the count says that
is all there is to zero. -/
theorem zeroBlocks_correct (avx : Bool) {F : Nat → Prop} (bytes : Nat) (hb : bytes ≤ 1024)
    (he : storeBytes avx * (bytes / storeBytes avx) = bytes)
    (hF : ∀ (m : Mem) (p : Addr), F (m.readW (p + 1024) 64).toNat → Proof.AesGcm.Flag.wipePreparedLen m p = bytes)
    (s₀ : State) (hp : (wipeX86_64 F).pre s₀) :
    ∃ t s', Exec isa (.block (zeroBlocks avx bytes)) s₀ t s' ∧ abiPreserved s₀ s' ∧
      (wipeX86_64 F).post s₀ s' := by
  obtain ⟨_, hwr, hlen, hret, hf⟩ := hp
  have hw : ∀ j < bytes / storeBytes avx,
      InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 (storeBytes avx * j)) (storeBytes avx) := fun j hj => by
    have : storeBytes avx * (j + 1) ≤ storeBytes avx * (bytes / storeBytes avx) := Nat.mul_le_mul_left _ hj
    rw [Nat.mul_succ, he] at this
    exact ⟨_, by rw [hwr]; exact List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  have hz := zeroBlocks_ok avx (bytes / storeBytes avx) s₀ (by rw [he]; omega) hw
  rw [he] at hz
  obtain ⟨t, s', hx, hg, hmx, hz, fr⟩ := hz
  refine ⟨t, s', hx, ⟨fun r _ => by rw [hg], ?_, by rw [hmx]⟩, ?_⟩
  · rw [hwr] at fr
    exact fr.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr; exact hret) (by decide)
  · show Spec.Aes.bytesAt _ _ _ = _
    rw [hF _ _ hf]
    exact prefix_spec hz

theorem zeroBlocks1024_ct (avx : Bool) (F : Nat → Prop) :
    ConstantTime isa (wipeX86_64 F).pre (wipeX86_64 F).pub (.block (zeroBlocks avx 1024)) := by
  cases avx <;>
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h

theorem zeroBlocks512_ct (avx : Bool) (F : Nat → Prop) :
    ConstantTime isa (wipeX86_64 F).pre (wipeX86_64 F).pub (.block (zeroBlocks avx 512)) := by
  cases avx <;>
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h

theorem zeroBlocks256_ct (avx : Bool) (F : Nat → Prop) :
    ConstantTime isa (wipeX86_64 F).pre (wipeX86_64 F).pub (.block (zeroBlocks avx 256)) := by
  cases avx <;>
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ h
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact h

/-- `wipePreparedContract` for the block that runs where the count satisfies
`C`, with no leak. -/
def wipeBranch (C : Nat → Prop) : Contract isa :=
  Proof.AesGcm.Flag.wipePreparedSig.contract X86_64.abi
    (pre := fun ctx m => C (m.readW (ctx + 1024) 64).toNat)
    (post := Proof.AesGcm.Flag.wipePreparedPost 64) (writeArgs := true)

/-- A state meeting `wipeBranch`'s precondition, with the count `v`. -/
def wipeSat (v : Byte) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x1400 then v else 0
  rd := []
  wr := [⟨0x1000, 1032⟩]

theorem wipe_implies48 : (wipeX86_64 (48 ≤ ·)).Implies (wipeBranch (48 ≤ ·)) := by
  sig_implies [wipeBranch, Proof.AesGcm.Flag.wipePreparedSig, Proof.AesGcm.Flag.wipePreparedPost, wipeX86_64,
    X86_64.abi, X86_64.argRegs] [wipeSat] using wipeSat 48

theorem wipe_implies16 : (wipeX86_64 fun c => ¬ 48 ≤ c ∧ 16 ≤ c).Implies
    (wipeBranch fun c => ¬ 48 ≤ c ∧ 16 ≤ c) := by
  sig_implies [wipeBranch, Proof.AesGcm.Flag.wipePreparedSig, Proof.AesGcm.Flag.wipePreparedPost, wipeX86_64,
    X86_64.abi, X86_64.argRegs] [wipeSat] using wipeSat 16

theorem wipe_implies0 : (wipeX86_64 fun c => ¬ 48 ≤ c ∧ ¬ 16 ≤ c).Implies
    (wipeBranch fun c => ¬ 48 ≤ c ∧ ¬ 16 ≤ c) := by
  sig_implies [wipeBranch, Proof.AesGcm.Flag.wipePreparedSig, Proof.AesGcm.Flag.wipePreparedPost, wipeX86_64,
    X86_64.abi, X86_64.argRegs] [wipeSat] using wipeSat 0

/-- The blocks of `wipe avx` on counts under 48: by the count, 512 bytes or
256. -/
theorem wipeLow_verified (avx : Bool) :
    Verified X86_64.target (Impl.Gcm.X86_64.Flag.onFlag 16 (.block (zeroBlocks avx 512)) (.block (zeroBlocks avx 256)))
      (Proof.AesGcm.Flag.wipePreparedSig.contract X86_64.abi
        (pre := fun ctx m => ¬ 48 ≤ (m.readW (ctx + 1024) 64).toNat)
        (post := Proof.AesGcm.Flag.wipePreparedPost 64) (writeArgs := true)
        (leak := some fun ctx m => [VG.X86_64.flagLeak m ctx])) :=
  Verified.of_onFlagCtx (Or.inl rfl) (by decide)
    (Verified.of_correct (zeroBlocks_correct avx 512 (by decide) (by cases avx <;> rfl)
      (fun m p h => by simp only [Proof.AesGcm.Flag.wipePreparedLen, Proof.AesGcm.Flag.powerCount, h.1, h.2, ↓reduceIte]))
      (zeroBlocks512_ct avx _) wipe_implies16)
    (Verified.of_correct (zeroBlocks_correct avx 256 (by decide) (by cases avx <;> rfl)
      (fun m p h => by simp only [Proof.AesGcm.Flag.wipePreparedLen, Proof.AesGcm.Flag.powerCount, h.1, h.2, ↓reduceIte]))
      (zeroBlocks256_ct avx _) wipe_implies0)
    (fun _ _ h₁ h₂ => ⟨h₁, h₂⟩) (fun _ _ h₁ h₂ => ⟨h₁, h₂⟩) (fun _ _ => rfl)
    (by obtain ⟨s, hs⟩ := wipe_implies0.sat
        exact ⟨s, pre_of_rel (name := "ctx") (w := true) (N := 129) (rest := []) (ret := none)
          (C := fun _ _ => True) (pre := fun ctx m => ¬ 48 ≤ (m.readW (ctx + 1024) 64).toNat ∧
            ¬ 16 ≤ (m.readW (ctx + 1024) 64).toNat)
          (fun _ _ h _ => h.1) hs trivial⟩)

/-- `vg_aes_gcm_wipe_prepared`, with AVX if `avx`. -/
theorem wipe_verified (avx : Bool) :
    Verified X86_64.target (wipe avx) (Proof.AesGcm.Flag.wipePreparedContract X86_64.abi) := by
  have h48 := Verified.leak_flag (name := "ctx") (rest := []) (ret := none)
    (leak := fun ctx m => [VG.X86_64.flagLeak m ctx])
    (Verified.of_correct (zeroBlocks_correct avx (F := (48 ≤ ·)) 1024 (by decide) (by cases avx <;> rfl)
      (fun m p h => by simp only [Proof.AesGcm.Flag.wipePreparedLen, Proof.AesGcm.Flag.powerCount, h, ↓reduceIte]))
      (zeroBlocks1024_ct avx _) wipe_implies48) (fun _ _ => rfl)
  have h := Verified.of_onFlagCtx (Or.inr rfl) (by decide) (leak := fun ctx m => [VG.X86_64.flagLeak m ctx,
      VG.X86_64.flagLeak m ctx]) h48 (wipeLow_verified avx)
    (fun _ _ _ h => h) (fun _ _ _ h => h) (fun _ _ => rfl)
    (by obtain ⟨s, hs⟩ := wipe_implies48.sat
        exact ⟨s, pre_of_rel (name := "ctx") (w := true) (N := 129) (rest := []) (ret := none)
          (C := fun _ _ => True) (pre := fun ctx m => 48 ≤ (m.readW (ctx + 1024) 64).toNat)
          (fun _ _ _ _ => trivial) hs trivial⟩)
  have key : ∀ v m, Curry.apply (Proof.AesGcm.Flag.wipePreparedSig.words abi.ptrBits)
      (fun ctx m => [VG.X86_64.flagLeak m ctx, VG.X86_64.flagLeak m ctx]) v m =
      Curry.apply (Proof.AesGcm.Flag.wipePreparedSig.words abi.ptrBits) (Proof.AesGcm.Flag.wipePreparedLeak abi.ptrBits) v m ++
        Curry.apply (Proof.AesGcm.Flag.wipePreparedSig.words abi.ptrBits) (Proof.AesGcm.Flag.wipePreparedLeak abi.ptrBits) v m := by
    intro v m; cases v <;> rfl
  exact Verified.leak_mono h fun v₁ v₂ m₁ m₂ e => by rw [key, key, e]

end VG.Proof.Gcm.X86_64.Prepare
