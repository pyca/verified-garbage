module

public import VerifiedGarbage.Impl.Dsa.Arm.Entry
public import VerifiedGarbage.Impl.Dsa.Arm.RandomSign
public import VerifiedGarbage.Proof.Dsa.Arm.RandomBodyCT
public import VerifiedGarbage.Proof.Dsa.Arm.RandomAttempt
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Contract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Proof.Weierstrass.PointContract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Impl.Dsa.Arm.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.PrivateKeyWitness
public import VerifiedGarbage.Proof.Dsa.Arm.SignCorrect
public import VerifiedGarbage.Proof.Dsa.Arm.SignCT
public import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedSignCT
import VerifiedGarbage.Proof.Dsa.Arm.PrevalidatedVerified

/-! ### `Dsa.Arm.RandomSignCT`, which only this module used -/

section

/-!
# The randomized signer is constant time (32-bit ARM)

The contract's public data (the arguments, the public key bytes, the status,
the consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign

theorem drop_take_prefix {α : Type} (xs : List α) {p q n : Nat} (h : p + q ≤ n) :
    (xs.drop p).take q = ((xs.take n).drop p).take q := by
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega_using [h])]

/-- Two entries with the same public data: the same arguments, q, public
key bytes, status and trace. -/
theorem random_public {s t : State} (H : (randomSignCheckedContract Arm.abi 144).pub s t) :
    pubOf s = pubOf t ∧ keyLeak s = keyLeak t ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [randomSignCheckedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero] at H
  obtain ⟨hsp, hleak, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := H
  change keyLeak s ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    keyLeak t ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : (keyLeak s).length = (keyLeak t).length := by
    simp only [keyLeak, Spec.Dsa.publicBytesLeak, rInput, List.length_map, List.length_take, rBytes_length,
      a0, a1, a2]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  refine ⟨?_, hk, hst, htr⟩
  have hargs : ∀ i < 9, stackArg s i = stackArg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega_using [hi]
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6, a7, a8]
  have hkey : (rInput s).key.take (3 * (rInput s).pLen + (rInput s).qLen) =
      (rInput t).key.take (3 * (rInput t).pLen + (rInput t).qLen) :=
    (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a1
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a2
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, by rw [r0, r1, r2, r3], List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [drop_take_prefix _ (n := 3 * (rInput s).pLen + (rInput s).qLen) (by omega_using []), hkey,
    drop_take_prefix (rInput t).key (n := 3 * (rInput t).pLen + (rInput t).qLen) (by omega_using []), hp, hq]

theorem alloc_push {s₀ : State} (A : RandomABI s₀) :
    isa.push (.alloc frameBytes) s₀ = some (allocated frameBytes s₀) := by
  have hsp : frameBytes ≤ s₀.sp.toNat := by have := A.stackLow; unfold frameBytes; omega_using [this]
  have hn : 0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧
      encodable (BitVec.ofNat 32 frameBytes) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_sign_random` leaks only what its contract makes public. -/
theorem randomSign_constantTime (S : Signer) (name : String) :
    ConstantTime isa (fun s => (randomSignCheckedContract Arm.abi 144).pre s ∧ RValid S s)
      (randomSignCheckedContract Arm.abi 144).pub (code name S.code) := by
  intro s t tsa tsb u w ⟨hs, Vs⟩ ⟨ht, Vt⟩ hpub ea eb
  have As := randomABI_of hs
  have At' := randomABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := random_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := body_ct S name _ _ _ _ _ _ ⟨⟨pubOf s, keyLeak s, (rResult s).status, (rResult s).trace⟩,
        ⟨s, As, rfl, ⟨rfl, rfl, rfl, Vs⟩, rfl⟩, ⟨t, At', e.symm, ⟨hk.symm, hst.symm, htr.symm, Vt⟩, rfl⟩⟩ hab hbb |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.Arm

end

end

/-! ### `Dsa.Arm.RandomSignCorrect`, which only this module used -/

section

/-!
# The randomized signer meets its contract (32-bit ARM)

`code` reserves its frame and runs the body (`body_ok`): on return the
callee-saved registers and `sp` are as on entry, and the status, `out` and
`used` are those of `Spec.Dsa.randomSignBytes`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.RandomSign
open VG.Proof.X25519.Arm (toNat_imm)

theorem code_ok (S : Signer) (name : String) {s₀ : State} (A : RandomABI s₀) (V : RValid S s₀) :
    WP isa (code name S.code) s₀ fun s' =>
      ∃ u m un, Finished s₀ u ∧ Frame [⟨State.addr (s₀.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩] u.mem m ∧
        s' = { freed frameBytes u with mem := m, unknowns := un } :=
  WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by have := A.stackLow; unfold frameBytes; omega_using [this])
    (WP.mono (body_ok S name A V) fun u hu m un hfl => ⟨u, m, un, hu, hfl, rfl⟩)

/-- `vg_dsa_sign_random` meets its contract. -/
theorem randomSign_correct (S : Signer) (name : String) (s : State)
    (hpre : (randomSignCheckedContract Arm.abi 144).pre s) (V : RValid S s) :
    ∃ t s', Exec isa (code name S.code) s t s' ∧ abiPreserved s s' ∧
      (randomSignCheckedContract Arm.abi 144).post s s' := by
  have A := randomABI_of hpre
  obtain ⟨t, s', he, u, m, un, hF, hfl, rfl⟩ := code_ok S name A V
  have fsub : Region.Sub ⟨State.addr (s.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ (rStack s) := by
    have := A.stackLow
    rw [FrameStack.addr_sub' (by unfold frameBytes; omega_using [this])]
    exact Offset.sub_below _ (by unfold frameBytes; omega_using []) (by unfold frameBytes; omega_using [])
  have dU : ∀ r ∈ [(⟨State.addr (s.sp - BitVec.ofNat 32 frameBytes), frameBytes⟩ : Region)], (rUsed s).Disjoint r := by
    intro r hr; obtain rfl := List.mem_singleton.mp hr; exact A.stackUsed.symm.sub_right fsub
  have out : Spec.Rsa.bytesAt m (State.addr (s.gpr .r0)) (s.gpr .r1).toNat =
      (rResult s).signature.getD (List.replicate (s.gpr .r1).toNat 0) := by
    rw [rBytes_frame hfl (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact A.stackOut.symm.sub_right fsub)
      (by have := (s.gpr .r1).isLt; omega_using [])]
    exact hF.out
  refine ⟨t, _, he, ⟨fun r hr => hF.regs r hr, by
    show u.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hF.sp, BitVec.sub_add_cancel]⟩, ?_⟩
  sig_post [randomSignCheckedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero]
  have hle := rResult_status_le A
  have hul : (rResult s).used < 2 ^ 32 := by
    have := rResult_used_le (s₀ := s)
    have : (rInput s).rand.length < 2 ^ 32 := by simp only [rInput, rBytes_length]; exact BitVec.isLt _
    omega_arith
  refine ⟨?_, out, ?_⟩
  · rw [BitVec.setWidth_append_eq_right]
    show (u.gpr .r0).toNat = (rResult s).status
    rw [hF.r0, toNat_imm (by omega_using [hle])]
  · show Spec.Rsa.wordsAt m (State.addr (s.gpr .r2)) 1 = [BitVec.ofNat 64 (rResult s).used]
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    refine congrArg (· :: []) (BitVec.eq_of_toNat_eq ?_)
    have := word_eq_w32 m (State.addr (s.gpr .r2)) 0
    simp only [Mont.word, w32, off] at this
    show (m.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 64).toNat = _
    rw [this, show (0 + 4 : Nat) = 4 from rfl]
    have lo : (m.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 32) = _ :=
      (hfl.readW (r := rUsed s) (Offset.contains_base _ (by decide) (by decide)) dU (by decide)).trans hF.usedLo
    have hi : (m.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 4) 32) = _ :=
      (hfl.readW (r := rUsed s) (Offset.contains_base _ (by decide) (by decide)) dU (by decide)).trans hF.usedHi
    rw [lo, hi, toNat_imm hul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hul])]
    rfl

end VG.Proof.Dsa.Arm

end

end


/-! # The 32-bit ARM randomized signers meet their contracts

`vg_dsa_sign_random`, which calls the fully checked signer, and
`vg_dsa_sign_random_prevalidated`, which calls the signer for a validated
private key. -/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.RandomSign

variable {umaal : Bool}

/-- A 1024/160 call with an empty tape: the output at `0x1000`, `used` at
`0x7000`, the key at `0x2000` and the working space at `0x8000`. -/
def randomSignSat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 40 | .r2 => 0x7000 | .r3 => 0x2000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0xa8 else if a = 0x20001 then 1 else if a = 0x20004 then 0x80
    else if a = 0x20008 then 20 else if a = 0x2000d then 0x50 else if a = 0x20015 then 0x60
    else if a = 0x2001d then 0x80 else if a = 0x20020 then 0x40 else if a = 0x20021 then 0x08 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x20000, 36⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

theorem randomSign_satisfiable : ∃ s, (randomSignCheckedContract Arm.abi 144).pre s := by
  sig_implies_sat [randomSignCheckedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
    [randomSignSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using randomSignSat

/-- The fully checked signer, which accepts every key. -/
def checkedSigner (umaal : Bool) : Signer where
  code := Entry.operation umaal true
  valid := fun _ _ _ => true
  correct := fun _ hs => let ⟨t, s', e, ha, hp⟩ := sign_correct hs.1; ⟨t, s', e, ha, hp⟩
  constantTime := fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => sign_constantTime _ _ _ _ _ _ h₁.1 h₂.1 hp e₁ e₂
  stack := sign_armStack

/-- The signer for a validated private key. -/
def prevalidatedSigner (umaal : Bool) : Signer where
  code := PrevalidatedSign.sign umaal
  valid := Spec.Dsa.validatePrivateKeyBytes
  correct := fun _ hs => let ⟨t, s', e, ha, hp⟩ := prevSign_correct hs; ⟨t, s', e, ha, hp⟩
  constantTime := prevSign_constantTime
  stack := by cases umaal <;> decide +kernel

theorem randomSign_verified (name : String) :
    Verified Arm.target (code name (Entry.operation umaal true)) (randomSignCheckedContract Arm.abi 144) :=
  ⟨fun s h => randomSign_correct (checkedSigner umaal) name s h rfl,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => randomSign_constantTime (checkedSigner umaal) name s₁ s₂ t₁ t₂ u₁ u₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩,
    randomSign_satisfiable⟩

/-- The randomized signer, calling the registered `vg_dsa_sign`. -/
theorem randomSigning_verified :
    Verified Arm.target (code ("vg_dsa_sign" ++ Impl.Mont.Arm.Dynamic.suffix umaal) (Entry.operation umaal true))
      (randomSignCheckedContract Arm.abi 144) :=
  randomSign_verified _

theorem randomPrevalidated_pre {s : State} (h : (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144).pre s) :
    (randomSignCheckedContract Arm.abi 144).pre s ∧ RValid (prevalidatedSigner umaal) s := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
  sig_and_intros <;> with_reducible assumption

/-- `randomSignSat` with `validPrivateKeyWitness` at `0x2000`. -/
def randomPrevSat : State where
  gpr := randomSignSat.gpr
  sp := randomSignSat.sp
  n := false
  z := false
  c := false
  v := false
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
    VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0 else randomSignSat.mem a
  rd := randomSignSat.rd
  wr := randomSignSat.wr

theorem randomPrevSat_key :
    Spec.Rsa.bytesAt randomPrevSat.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness :=
  bytesAt_window (base := 0x2000) VG.Proof.Dsa.validPrivateKeyWitness_length (by decide) fun _ h₁ h₂ =>
    ite_eq_left ⟨h₁, h₂⟩

theorem randomPrev_satisfiable : ∃ s, (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144).pre s := by
  refine ⟨randomPrevSat, ?_⟩
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
  sig_and_intros
  -- The key's validity, the last goal, by the witness's own proof: `decide +kernel` would have
  -- the kernel validate the key again, read byte by byte from the state's memory.
  on_goal -1 =>
    change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt randomPrevSat.mem 0x2000 424) = true
    rw [randomPrevSat_key]
    exact VG.Proof.Dsa.validPrivateKeyWitness_valid
  all_goals first
    | decide +kernel
    | exact Region.disjoint_of_sep (by decide +kernel)

theorem randomSignPrevalidated_verified (name : String) :
    Verified Arm.target (code name (PrevalidatedSign.sign umaal))
      (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144) :=
  ⟨fun s h => randomSign_correct (prevalidatedSigner umaal) name s
      (randomPrevalidated_pre (umaal := umaal) h).1 (randomPrevalidated_pre h).2,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => randomSign_constantTime (prevalidatedSigner umaal) name s₁ s₂ t₁ t₂ u₁ u₂
      (randomPrevalidated_pre h₁) (randomPrevalidated_pre h₂),
    randomPrev_satisfiable⟩

/-- The randomized signer for a validated key, calling the registered
`vg_dsa_sign_prevalidated`. -/
theorem randomSigningPrevalidated_verified :
    Verified Arm.target (code (PrevalidatedSign.signerName umaal) (PrevalidatedSign.sign umaal))
      (Spec.Dsa.randomSignPrevalidatedContract Arm.abi 144) :=
  randomSignPrevalidated_verified _

end VG.Proof.Dsa.Arm
