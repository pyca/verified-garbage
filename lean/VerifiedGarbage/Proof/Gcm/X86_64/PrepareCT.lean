module

public import VerifiedGarbage.Impl.Gcm.X86_64.Prepare
public import VerifiedGarbage.Impl.Gcm.X86_64.PrepareAvx
import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Spec.Gcm.Prepared
public import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Gcm.X86_64.Prepare
meta import VerifiedGarbage.Impl.Gcm.X86_64.PrepareAvx
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Spec.Gcm.Prepared
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Preparing a key context's powers in place: the contract on the registers

`prepareX86_64`, `vg_aes_gcm_prepare`'s contract on the registers; the
constant time of its implementations (`prepare_ct`): only the context's
address affects timing; and `verified_of`, which proves `Verified` for any
code that writes the prepared powers and nothing else (`PrepOk`). The field,
where each implementation's powers are proven, is in `Stitch/Ok.lean` and
`StitchAvx8/Ok.lean`, so that its algebra reaches no new module.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.Prepare

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Prepare (prepare)

/-- `vg_aes_gcm_prepare`'s contract, on the registers. -/
def prepareX86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1024⟩] ∧ (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1024⟩
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    Spec.Gcm.PreparedPowersRepr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

theorem prepare_ct : ConstantTime isa prepareX86_64.pre prepareX86_64.pub prepare := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem prepareAvx_ct :
    ConstantTime isa prepareX86_64.pre prepareX86_64.pub Impl.Gcm.X86_64.PrepareAvx.prepare := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

/-- What `vg_aes_gcm_prepare` does from `s₀`: the 48 prepared powers of the
hash subkey at `C + 240` into pairs 0–23 of the context at `C`, nothing else
written, and the registers but `rax` kept. -/
def PrepOk (s₀ s : State) : Prop :=
  (∀ k < 24, ∀ l < 2, s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256 + 32 * k + 16 * l)) 128 =
    Spec.Gcm.preparedPower (Spec.Gcm.hpow (Spec.Gcm.ctxH s₀.mem (s₀.gpr .rdi)) (2 * k + 2 - l))) ∧
  Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩] s₀.mem s.mem ∧
  (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr


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
