module

public import VerifiedGarbage.Proof.Dsa.Arm.Key.Frame
public import VerifiedGarbage.Impl.Dsa.Arm.GenerateKey
public import VerifiedGarbage.Proof.Framework.Arm.Contract
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Two
public import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Impl.Dsa.Arm.Generate
import VerifiedGarbage.Proof.Dsa.Arm.Key.BodyCT
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arm.Key.Body
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.TCB.Arm.Target

/-! ### `Dsa.Arm.Key.CT`, which only this module used -/

section

/-!
# DSA key generation is constant time (32-bit ARM)

The contract's public data (the arguments, the domain, the status, the
consumption and the trace) gives two entries the same `BodyPub`, and the
frame's allocation leaks nothing.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey

variable {umaal : Bool}

/-- Two entries with the same public data: the same arguments, domain,
status and trace. -/
theorem key_public {s t : State} (H : (Spec.Dsa.generateKeyContract Arm.abi 144).pub s t) :
    pubOf s = pubOf t ∧ (rInput s).key = (rInput t).key ∧ (rResult s).status = (rResult t).status ∧
      (rResult s).trace = (rResult t).trace := by
  sig_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero] at H
  obtain ⟨hsp, hleak, r0, r1, r2, r3, a0, a1, a2, a3, a4, a5, a6⟩ := H
  change (rInput s).key.map (·.toNat) ++ [(rResult s).status, (rResult s).used] ++ (rResult s).trace =
    (rInput t).key.map (·.toNat) ++ [(rResult t).status, (rResult t).used] ++ (rResult t).trace at hleak
  have hlen : ((rInput s).key.map (·.toNat)).length = ((rInput t).key.map (·.toNat)).length := by
    simp only [rInput, List.length_map, rBytes_length, a0]
  rw [List.append_assoc, List.append_assoc] at hleak
  obtain ⟨hk, hrest⟩ := List.append_inj hleak hlen
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  obtain ⟨hst, -, htr⟩ := hrest
  have hkey : (rInput s).key = (rInput t).key := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hk
  refine ⟨?_, hkey, hst, htr⟩
  have hargs : ∀ i < 7, stackArg s i = stackArg t i := by
    intro i hi
    have c : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega_using [hi]
    rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [a0, a1, a2, a3, a4, a5, a6]
  have hp : (rInput s).pLen = (rInput t).pLen := congrArg BitVec.toNat a1
  have hq : (rInput s).qLen = (rInput t).qLen := congrArg BitVec.toNat a2
  simp only [pubOf, Pub.mk.injEq]
  refine ⟨hsp, by rw [r0, r1, r2, r3], List.map_congr_left fun i hi => hargs i (List.mem_range.mp hi), ?_⟩
  unfold rQBytes
  rw [hkey, hp, hq]

theorem alloc_push {s₀ : State} (A : KeyABI s₀) :
    isa.push (.alloc frameBytes) s₀ = some (allocated frameBytes s₀) := by
  have hsp : frameBytes ≤ s₀.sp.toNat := by have := A.stackLow; unfold frameBytes; omega_using [this]
  have hn : 0 < frameBytes ∧ frameBytes < 4096 ∧ frameBytes % 8 = 0 ∧
      encodable (BitVec.ofNat 32 frameBytes) = true := by decide
  simp only [isa, push, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, hsp, and_self, ite_true]
  rfl

/-- `vg_dsa_generate_key` leaks only what its contract makes public. -/
theorem generateKey_constantTime (check derive : String) :
    ConstantTime isa (Spec.Dsa.generateKeyContract Arm.abi 144).pre
      (Spec.Dsa.generateKeyContract Arm.abi 144).pub
      (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have As := keyABI_of hs
  have At' := keyABI_of ht
  obtain ⟨e, hk, hst, htr⟩ := key_public hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [alloc_push As, Option.some.injEq] at hap
      rw [alloc_push At', Option.some.injEq] at hbp
      subst hap hbp
      have hh := body_ct check derive _ _ _ _ _ _
        ⟨⟨pubOf s, (rInput s).key, (rResult s).status, (rResult s).trace⟩,
        ⟨s, As, rfl, ⟨rfl, rfl, rfl⟩, rfl⟩, ⟨t, At', e.symm, ⟨hk.symm, hst.symm, htr.symm⟩, rfl⟩⟩ hab hbb |>.1
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.Arm.Key

end

end

/-! ### `Dsa.Arm.Key.Correct`, which only this module used -/

section

/-!
# DSA key generation on 32-bit ARM: correctness

`generateKey_correct`: from the shared contract's precondition,
`vg_dsa_generate_key` returns the status of `Spec.Dsa.generateKeyBytes`,
writes its key (or zeros) and publishes its consumption as a 64-bit count,
and restores the registers the ABI preserves.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Proof.Mont VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.Random VG.Impl.Dsa.Arm.GenerateKey
open VG.Proof.X25519.Arm (toNat_imm)

variable {umaal : Bool}

theorem rResult_used_le {s₀ : State} (A : KeyABI s₀) : (rResult s₀).used ≤ (rInput s₀).rand.length := by
  rw [rResult_eq A]
  split
  · split
    all_goals
      have := VG.Proof.Dsa.Random.sample_used_le (rq s₀) 128 ((rInput s₀).rand.drop 0)
      simpa [spl] using this
  · exact Nat.zero_le _

theorem code_ok (check derive : String) {s₀ : State} (A : KeyABI s₀) :
    WP isa (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) s₀ fun s' => ∃ u, Finished s₀ u ∧ s' = freed frameBytes u :=
  WP.alloc ⟨by decide, by decide, by decide, by decide⟩ (by have := A.stackLow; unfold frameBytes; omega_using [this])
    (WP.mono (body_ok check derive A) fun u hu => ⟨u, hu, rfl⟩)

/-- `vg_dsa_generate_key` meets its contract. -/
theorem generateKey_correct (check derive : String) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract Arm.abi 144).pre s) :
    ∃ t s', Exec isa (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal)) s t s' ∧
      abiPreserved s s' ∧ (Spec.Dsa.generateKeyContract Arm.abi 144).post s s' := by
  have A := keyABI_of hpre
  obtain ⟨t, s', he, u, hF, rfl⟩ := code_ok check derive A
  refine ⟨t, _, he, ⟨fun r hr => hF.regs r hr, by
    show u.sp + BitVec.ofNat 32 frameBytes = s.sp
    rw [hF.sp, BitVec.sub_add_cancel]⟩, ?_⟩
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.stackArgAddr, BitVec.add_zero]
  have hle := rResult_status_le A
  have hul : (rResult s).used < 2 ^ 32 := by
    have := rResult_used_le A
    have : (rInput s).rand.length < 2 ^ 32 := by simp only [rInput, rBytes_length]; exact BitVec.isLt _
    omega_arith
  refine ⟨?_, hF.out, ?_⟩
  · rw [BitVec.setWidth_append_eq_right]
    show (u.gpr .r0).toNat = (rResult s).status
    rw [hF.r0, toNat_imm (by omega_using [hle])]
  · show Spec.Rsa.wordsAt u.mem (State.addr (s.gpr .r2)) 1 = [BitVec.ofNat 64 (rResult s).used]
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero]
    refine congrArg (· :: []) (BitVec.eq_of_toNat_eq ?_)
    have := word_eq_w32 u.mem (State.addr (s.gpr .r2)) 0
    simp only [Mont.word, w32, off] at this
    show (u.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 64).toNat = _
    rw [this, show (0 + 4 : Nat) = 4 from rfl]
    have lo : (u.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 0) 32) = _ := hF.usedLo
    have hi : (u.mem.readW (State.addr (s.gpr .r2) + BitVec.ofNat 64 4) 32) = _ := hF.usedHi
    rw [lo, hi, toNat_imm hul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hul])]
    rfl

end VG.Proof.Dsa.Arm.Key

end

end


/-! # 32-bit ARM DSA key generation meets its contract -/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Key

open VG VG.Arm VG.Impl.Dsa.Arm VG.Impl.Dsa.Arm.GenerateKey

variable {umaal : Bool}

/-- A 1024/160 call with an empty tape: the output at `0x1000`, `used` at
`0x7000`, the domain at `0x2000` and the working space at `0x8000`. -/
def generateKeySat : State where
  gpr r := match r with | .r0 => 0x1000 | .r1 => 424 | .r2 => 0x7000 | .r3 => 0x2000 | _ => 0
  sp := 0x20000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x20000 then 0x14 else if a = 0x20001 then 1 else if a = 0x20004 then 0x80
    else if a = 0x20008 then 20 else if a = 0x2000d then 0x50 else if a = 0x20015 then 0x80
    else if a = 0x20019 then 0x24 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩, ⟨0x20000, 28⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩]

theorem generateKey_satisfiable : ∃ s, (Spec.Dsa.generateKeyContract Arm.abi 144).pre s := by
  sig_implies_sat [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, Arm.stackArgAddr, BitVec.add_zero]
    [generateKeySat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read] using generateKeySat

theorem generateKey_verified (check derive : String) :
    Verified Arm.target (code check derive (Generate.checkParameters umaal) (Generate.deriveChecked umaal))
      (Spec.Dsa.generateKeyContract Arm.abi 144) :=
  ⟨generateKey_correct check derive, generateKey_constantTime check derive, generateKey_satisfiable⟩

/-- Key generation, calling `vg_dsa_check_parameters` and the internal
`vg_dsa_derive_key_checked`. -/
theorem generating_verified :
    Verified Arm.target (code (Generate.checkName umaal) (Generate.deriveName umaal) (Generate.checkParameters umaal)
      (Generate.deriveChecked umaal)) (Spec.Dsa.generateKeyContract Arm.abi 144) :=
  generateKey_verified _ _

end VG.Proof.Dsa.Arm.Key
