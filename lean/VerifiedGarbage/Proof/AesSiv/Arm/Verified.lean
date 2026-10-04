import VerifiedGarbage.Proof.AesSiv.Arm.CTEnc
import VerifiedGarbage.Proof.AesSiv.Arm.CTInit
import VerifiedGarbage.Proof.AesSiv.Scratch
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RegScratch

/-!
# AES-SIV on ARMv7: `Verified`

Untrusted: everything here is checked by Lean. Correctness and constant
time, a state satisfying each precondition, and the shared contracts of
`Spec/Siv/Contract.lean`. `init` calls `vg_cmac_aes_subkeys`, which uses 8
bytes of stack, and keeps its 2560-byte working space in a frame of its own
(`init_framed`); `encrypt` and `decrypt` use 16 bytes: each call pushes two
words, and `vg_cmac_aes_update` and `vg_cmac_aes_finalize` push two more for
their own calls. On ARMv7 the arguments on the stack are read-only, so the
writable regions are the data and `work`, as the proofs take them (`E0`).
-/

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Impl.AesSiv.Arm

/-- A state with the given registers, the stack pointer at `0x8000`, memory
of zeros (so stack arguments of 0) and the given regions. -/
def sivSat (g : Reg → BitVec 32) (rd wr : List Region) : State where
  gpr := g
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := rd
  wr := wr

/-! ## `vg_aes_siv_init` -/

/-- A state satisfying `vg_aes_siv_init`'s precondition. -/
def initSat : State :=
  sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0)
    [⟨0x1000, 32⟩] [⟨0x2000, 512⟩, ⟨0x3000, 2560⟩]

theorem init_verified : Verified Arm.target init (Proof.AesSiv.initScratchContract Arm.abi 8) :=
  Verified.of_correct (fun _ hs => init_wp hs) init_ct (by
    sig_implies [Proof.AesSiv.initScratchContract, Proof.AesSiv.initScratchSig, Spec.Siv.initPre,
      Spec.Siv.initPost, initArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [initSat, sivSat] using initSat)

/-- A state satisfying `vg_aes_siv_init`'s precondition, without the
working space. -/
def initFrameSat : State :=
  sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 32 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 32⟩] [⟨0x2000, 512⟩]

theorem initFrameSat_pre : ∃ s, (Spec.Siv.initContract Arm.abi 2568).pre s := by
  implies_sat [Spec.Siv.initContract, Spec.Siv.initSig, Spec.Siv.initPre, Spec.Siv.initPost,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [initFrameSat, sivSat] using initFrameSat

/-- `init` with its working space in a frame of 2560 bytes. -/
theorem init_framed : Verified Arm.target (Impl.StackScratch.Arm.withRegScratch 2560 .r3 init)
    (Spec.Siv.initContract Arm.abi 2568) :=
  Arm.Verified.regScratch (sig := Spec.Siv.initSig) (nm := "scratch") (e := .u64) (n := 320)
    (pre := Spec.Siv.initPre Arm.abi.ptrBits) (post := Spec.Siv.initPost Arm.abi.ptrBits)
    (wa := true) (stack := 8) init_verified (by decide) (by decide) (by decide) initFrameSat_pre

/-! ## `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` -/

theorem filter_true' (l : List Region) : l.filter (fun _ => true) = l := List.filter_eq_self.mpr (by simp)

theorem filter_false' (l : List Region) : l.filter (fun _ => false) = [] := List.filter_eq_nil_iff.mpr (by simp)

theorem filterMap_some' {β : Type} (f : Region → β) (l : List Region) :
    l.filterMap (fun x => some (f x)) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem filterMap_none' {β : Type} (l : List Region) : l.filterMap (fun _ => (none : Option β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem cov_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-- Component `i`'s region, as the descriptors list it. -/
theorem listed_mem (m : Mem) (a : BitVec 32) {N i : Nat} (hi : i < N) :
    (⟨State.addr (descW m a i 0), (descW m a i 1).toNat⟩ : Region) ∈ Sig.listed 32 m .u8 (State.addr a) N := by
  refine List.mem_map.mpr ⟨i, List.mem_range.mpr hi, ?_⟩
  simp only [descW, State.addr, Elem.size, Nat.mul_one]
  rw [show i * (2 * (32 / 8)) = 8 * i + 4 * 0 by omega, show (32 / 8 : Nat) = 4 from rfl, BitVec.add_assoc,
    BitVec.ofNat_add_ofNat, show 8 * i + 4 * 0 + 4 = 8 * i + 4 * 1 by omega]

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = State.addr s.sp := by
  simp [stackArgAddr]

/-- The shared contracts' precondition gives the proofs' entry invariant,
with the descriptors' words in the entry memory. -/
theorem encPre_of {s : State} (h : (Spec.Siv.encryptContract Arm.abi 16).pre s) :
    E0 (s.gpr .r0) (stackArg s 2) s.sp (s.gpr .r2) (stackArg s 0) (s.gpr .r1).toNat (s.gpr .r3).toNat
      (stackArg s 1).toNat (fun i j => descW s.mem (s.gpr .r2) i j) s := by
  sig_pre [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    Arm.State.addr, List.append_eq] at h
  sig_split h
  simp only [List.filter_map, List.map_map, List.filterMap_map, List.map_nil, Function.comp_def,
    Bool.not_false, filter_true', filter_false', filterMap_some',
    filterMap_none', List.map_id', Sig.conj_cons, Sig.conj_append, Sig.conj_map, Bool.cond_false,
    List.nil_append, Sig.conj, List.filter_append, List.filter_cons, List.map_append,
    List.filterMap_append, List.filterMap_cons, ite_true, Bool.false_eq_true, ite_false, List.filter_nil,
    List.filterMap_nil, List.map_cons] at *
  rename_i sp16 afit cd bc bd bw fc fd fw hrd hwr pw bl fl
  obtain ⟨cW, dW, dA, ⟨dL, dArg⟩, wA, ⟨wL, wArg⟩, -⟩ := pw
  obtain ⟨bA, bL, -⟩ := bl
  obtain ⟨fA, fL⟩ := fl
  rw [stackArgAddr0] at hrd wArg dArg
  have hA : (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 := by omega
  have inRd {r : Region} (hr : r ∈ s.rd) : r ∈ s.rd ++ s.wr := List.mem_append_left _ hr
  have inWr {r : Region} (hr : r ∈ s.wr) : r ∈ s.rd ++ s.wr := List.mem_append_right _ hr
  have e4 : State.addr (s.sp + BitVec.ofNat 32 4) = State.addr s.sp + BitVec.ofNat 64 4 := addr_add (by omega)
  have e8 : State.addr (s.sp + BitVec.ofNat 32 8) = State.addr s.sp + BitVec.ofNat 64 8 := addr_add (by omega)
  have mC : (⟨State.addr (s.gpr .r0), 512⟩ : Region) ∈ s.rd := by rw [hrd]; exact List.mem_cons_self
  have mA : (⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩ : Region) ∈ s.rd := by
    rw [hrd, Nat.mul_comm]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have mS : (⟨State.addr s.sp, 12⟩ : Region) ∈ s.rd := by
    rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  have mD : (⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_self
  have mW : (⟨State.addr (stackArg s 2), 2576⟩ : Region) ∈ s.wr := by
    rw [hwr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨⟨⟨fc, fw, sp16, cW, bc, bw⟩, ⟨cov_mem (inRd mC), cov_mem mW⟩,
    rfl, by simp, rfl, by simp, rfl, h, afit, cov_mem (inRd mS), wArg.symm, dArg.symm, ?_, ?_, ?_,
    ⟨cov_mem (inRd mA), hA, by rw [Nat.mul_comm]; exact wA.symm, by rw [Nat.mul_comm]; exact bA, fun i hi => ?_⟩,
    ⟨⟨cov_mem (inWr mD), fd, dW, bd⟩, cov_mem mD, cd⟩, BitVec.isLt _⟩, hwr, fun _ _ _ _ => rfl⟩
  · rw [stackArg, stackArgAddr0]
  · rw [stackArg, stackArgAddr, show 4 * 1 = 4 from rfl, e4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [stackArg, stackArgAddr, show 4 * 2 = 8 from rfl, e8]
  · have hm := listed_mem s.mem (s.gpr .r2) hi
    have f := fL _ hm
    have mP : (⟨State.addr (descW s.mem (s.gpr .r2) i 0), (descW s.mem (s.gpr .r2) i 1).toNat⟩ : Region) ∈
        s.rd := by
      rw [hrd]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hm))
    exact ⟨cov_mem (inRd mP), f, (wL _ hm).symm, bL _ hm⟩

/-- Descriptors whose bytes are the same in two memories have the same words. -/
theorem descW_eq {m m' : Mem} {a : BitVec 32} {N : Nat}
    (h : ∀ k < N * 8, m (State.addr a + BitVec.ofNat 64 k) = m' (State.addr a + BitVec.ofNat 64 k))
    {i j : Nat} (hi : i < N) (hj : j < 2) : descW m' a i j = descW m a i j := by
  have e := Mem.read_congr (m := m) (m' := m') (a := State.addr a + BitVec.ofNat 64 (8 * i + 4 * j))
    (n := 32 / 8) fun k hk => by rw [Offset.add_add]; exact h _ (by omega)
  simp only [descW, Mem.readW, e]

/-- The second run's entry invariant, with the first run's public values. -/
theorem encPre_pub {s₁ s₂ : State} (h₂ : (Spec.Siv.encryptContract Arm.abi 16).pre s₂)
    (q : s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2)
    (hd : ∀ k < (s₁.gpr .r3).toNat * 8, s₁.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 k) =
      s₂.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 k)) :
    E0 (s₁.gpr .r0) (stackArg s₁ 2) s₁.sp (s₁.gpr .r2) (stackArg s₁ 0) (s₁.gpr .r1).toNat (s₁.gpr .r3).toNat
      (stackArg s₁ 1).toNat (fun i j => descW s₁.mem (s₁.gpr .r2) i j) s₂ := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7⟩ := q
  have E := encPre_of h₂
  have hd' : DescEq s₂.mem (s₁.gpr .r2) (s₁.gpr .r3).toNat (fun i j => descW s₁.mem (s₁.gpr .r2) i j) :=
    fun i hi j hj => descW_eq hd hi hj
  rw [q3, q4] at hd'
  rw [q0, q1, q2, q3, q4, q5, q6, q7]
  exact ⟨E.pre, E.wr, hd'⟩

/-- `vg_aes_siv_encrypt` and `vg_aes_siv_decrypt` are constant time, given
their constant time on the entry invariant. -/
theorem enc_ct {c : Prog isa} {k : Contract isa} (hk : ∀ s, k.pre s → (Spec.Siv.encryptContract Arm.abi 16).pre s)
    (hpub : ∀ s₁ s₂, k.pub s₁ s₂ → (s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
      s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2) ∧
      ∀ i < (s₁.gpr .r3).toNat * 8, s₁.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 i) =
        s₂.mem (State.addr (s₁.gpr .r2) + BitVec.ofNat 64 i))
    (hc : ∀ {c' w sp a D : BitVec 32} {R N n : Nat} {dsc : Nat → Nat → BitVec 32}, Lay c' w sp →
      (R = 10 ∨ R = 12 ∨ R = 14) → N < 2 ^ 32 → n < 2 ^ 32 → Proof.AesGcm.Arm.CT (E0 c' w sp a D R N n dsc) c) :
    ConstantTime isa k.pre k.pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hq e₁ e₂
  have E₁ := encPre_of (hk _ h₁)
  obtain ⟨q, hd⟩ := hpub _ _ hq
  exact (hc E₁.pre.lay E₁.pre.rounds (BitVec.isLt _) (BitVec.isLt _) _ _ _ _ _ _
    ⟨E₁, encPre_pub (hk _ h₂) q hd⟩ e₁ e₂).1

/-- A state satisfying the precondition of `vg_aes_siv_encrypt` and
`vg_aes_siv_decrypt`, with no associated data, no data and `work` at 0. -/
def encSat : State :=
  sivSat (fun r => match r with | .r0 => 0x1000 | .r1 => 10 | .r2 => 0x2000 | _ => 0)
    [⟨0x1000, 512⟩, ⟨0x2000, 0⟩, ⟨0x8000, 12⟩] [⟨0, 0⟩, ⟨0, 2576⟩]

theorem encSat_pre : ∃ s, (Spec.Siv.encryptContract Arm.abi 16).pre s := by
  sig_implies_sat [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr] [encSat, sivSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
    using encSat

theorem encrypt_verified : Verified Arm.target encrypt (Spec.Siv.encryptContract Arm.abi 16) := by
  refine ⟨fun s hs => ?_, enc_ct (fun _ h => h) (fun s₁ s₂ hp => ?_)
    (fun L hR hN hn => encrypt_ct L hR hN hn), encSat_pre⟩
  · have E := encPre_of hs
    obtain ⟨t, s', he, hq⟩ := encrypt_wp E.pre.lay E.pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr]
    exact hq.2
  · sig_pub [Spec.Siv.encryptContract, Spec.Siv.encryptSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val, Arm.State.addr] at hp
    sig_split hp
    rename_i q0 q1 q2 q3 q4 q5 q6 q7
    exact ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7⟩, hp⟩

theorem decrypt_verified : Verified Arm.target decrypt (Spec.Siv.decryptContract Arm.abi 16) := by
  have hpre : ∀ s, (Spec.Siv.decryptContract Arm.abi 16).pre s → (Spec.Siv.encryptContract Arm.abi 16).pre s :=
    fun _ h => h
  refine ⟨fun s hs => ?_, enc_ct hpre (fun s₁ s₂ hp => ?_) (fun L hR hN hn => decrypt_ct L hR hN hn),
    encSat_pre⟩
  · have E := encPre_of (hpre _ hs)
    obtain ⟨t, s', he, hq⟩ := decrypt_wp E.pre.lay E.pre
    refine ⟨t, s', he, hq.1, ?_⟩
    sig_post [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    have e : ∀ x y : BitVec 32, (x ++ y).setWidth 32 = y := fun _ _ => BitVec.setWidth_append_eq_right
    rw [e]
    exact hq.2
  · sig_pub [Spec.Siv.decryptContract, Spec.Siv.decryptSig, Spec.Siv.encryptSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] at hp
    sig_split hp
    rename_i q0 _ q1 q2 q3 q4 q5 q6 q7
    exact ⟨⟨q0, q1, q2, q3, q4, q5, q6, q7⟩, hp⟩

end VG.Proof.AesSiv.Arm
