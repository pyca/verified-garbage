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

/-- What `vg_aes_gcm_prepare` does from `s₀`: the 48 prepared powers of the
hash subkey at `C + 240` into pairs 0–23 of the context at `C`, nothing else
written, and the registers but `rax` and `r11` kept. -/
def PrepOk (s₀ s : State) : Prop :=
  (∀ k < 24, ∀ l < 2, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (2 * k + 2 - l))) ∧
  Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩] s₀.mem s.mem ∧
  (∀ r, r ≠ .rax → r ≠ .r11 → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr


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

/-! `vg_aes_gcm_prepare` on the 1088-byte prepared key context, whose word at
byte 1024 says whether the powers are absent (`Proof.AesGcm.Flag.PreparedRepr`): the
code that computes none (`prepareAbsent`), and each implementation that
computes them, after setting that word to 0 (`prepareFlagged`). -/

namespace VG.Proof.Gcm.X86_64.Prepare

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Flag (storeFlag prepareAbsent prepareFlagged)

/-- `vg_aes_gcm_prepare`'s contract on the prepared key context, on the
registers. -/
def flaggedX86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1088⟩] ∧ (s.gpr .rdi).toNat + 1088 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1088⟩
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
  wr := [⟨0x1000, 1088⟩]

theorem flagged_implies : flaggedX86_64.Implies (Proof.AesGcm.Flag.prepareContract X86_64.abi) := by
  sig_implies [Proof.AesGcm.Flag.prepareContract, Proof.AesGcm.Flag.prepareSig, Proof.AesGcm.Flag.preparePost,
    flaggedX86_64, X86_64.abi, X86_64.argRegs] [flaggedSat] using flaggedSat

/-- `storeFlag v` from `s₀`: the flag word is `v`, and only it and `rax`
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
    {d k : Nat} (hdk : d + k ≤ 1088) (fr : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 d, k⟩] s₁.mem s.mem)
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
  obtain ⟨t, s', he, hm, hg, _, _⟩ := storeFlag_run 1 s₀ (flagged_pre hp)
  have fr : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 1024, 8⟩] s₀.mem s'.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨t, s', he, abiPreserved_of_exec (by rfl) he
    (flagged_gpr hp hm hg (d := 1024) (k := 8) (by decide) (Frame.refl _ _) fun _ _ _ => rfl), ?_, Or.inl ?_⟩
  · exact bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  · rw [hm]; exact Mem.readW_writeW_self64 _ _ _

/-- `vg_aes_gcm_prepare` computing no powers. -/
theorem absent_verified : Verified X86_64.target prepareAbsent (Proof.AesGcm.Flag.prepareContract X86_64.abi) :=
  Verified.of_correct absent_correct absent_ct flagged_implies

/-- `prepareFlagged c`, for code `c` that writes the prepared powers and
nothing else (`PrepOk`). -/
theorem flagged_correct {c : Prog isa}
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 →
      WP isa c s₀ (PrepOk s₀))
    (hx : c.allInstrs (fun i => !loadsMxcsr i) = true) (s₀ : State) (hp : flaggedX86_64.pre s₀) :
    ∃ t s', Exec isa (prepareFlagged c) s₀ t s' ∧ abiPreserved s₀ s' ∧ flaggedX86_64.post s₀ s' := by
  have hx' : (prepareFlagged c).allInstrs (fun i => !loadsMxcsr i) = true := by
    simp only [prepareFlagged, Code.allInstrs, hx, Bool.and_true]; rfl
  have hwrap := hp.2.2.1
  have hwr := hp.2.1
  have hW : WP isa (prepareFlagged c) s₀ fun s => gprPreserved s₀ s ∧ flaggedX86_64.post s₀ s := by
    rw [prepareFlagged, WP.seq_iff]
    refine WP.mono (storeFlag_run 0 s₀ (flagged_pre hp)) fun s₁ ⟨hm₁, hg₁, _, hwr₁⟩ => ?_
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
    refine ⟨flagged_gpr hp hm₁ hg₁ (by decide) fr g, keep.trans keep₁, Or.inr fun k hk => ?_⟩
    rw [hH]
    have p0 := pw k hk 0 (by decide)
    have p1 := pw k hk 1 (by decide)
    rw [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] at p0
    rw [show 256 + 32 * k + 16 * 1 = 272 + 32 * k by omega, show 2 * k + 2 - 1 = 2 * k + 1 by omega] at p1
    exact ⟨p0, p1⟩
  obtain ⟨t, s', he, hg, hpost⟩ := hW
  exact ⟨t, s', he, abiPreserved_of_exec hx' he hg, hpost⟩

/-- `Verified` for `prepareFlagged c`, for code `c` that writes the prepared
powers and nothing else, loads no MXCSR, and is constant time. -/
theorem flagged_verified (c : Prog isa)
    (hok : ∀ s₀, InRegions s₀.wr (s₀.gpr .rdi) 1024 → (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 →
      WP isa c s₀ (PrepOk s₀))
    (hx : c.allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged c)) :
    Verified X86_64.target (prepareFlagged c) (Proof.AesGcm.Flag.prepareContract X86_64.abi) :=
  Verified.of_correct (flagged_correct hok hx) hct flagged_implies

/-- The constant time of each implementation that computes the powers, after
`storeFlag 0`. -/
theorem flaggedZ_ct :
    ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged Impl.Gcm.X86_64.PrepareZ.prepare) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem flagged16_ct :
    ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged Impl.Gcm.X86_64.Prepare16.prepare) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem flaggedAvx_ct :
    ConstantTime isa flaggedX86_64.pre flaggedX86_64.pub (prepareFlagged Impl.Gcm.X86_64.PrepareAvx.prepare) := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

end VG.Proof.Gcm.X86_64.Prepare
