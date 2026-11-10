module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Correct
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.PrimesCall
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
meta import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.X86.Taint
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Impl.Bignum.X86.PrivPre

/-! # `vg_rsa_private_precompute` on x86: constant time but for `n`

Two runs from states that agree on what the contract makes public (`Pub`:
`esp`, the arguments and `n`'s bytes) give their callees the same arguments,
regions and `n` (`pc_pub`, `pr_pub`); the blocks are checked by the taint
analysis with only `esp` public, and the loops with their pointers and
counts public, which the runs agree on.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (body code copyPrimes copyPrime copyLoop dstAt slotSrc primeWords shl maskLoop
  primes statusOffset)

/-- What two runs agree on. -/
structure Pub (s₁ s₂ : State) : Prop where
  sp : s₁.gpr .esp = s₂.gpr .esp
  n : nBytes s₁ = nBytes s₂
  args : ∀ i < 10, arg s₁ i = arg s₂ i

theorem pub_of {s₁ s₂ : State} (h : (Spec.Rsa.privatePrecomputeContract abi stackBytes).pub s₁ s₂) :
    Pub s₁ s₂ := by
  sig_pub [Spec.Rsa.privatePrecomputeContract, Spec.Rsa.privatePrecomputeSig, abi, argSlots, argVal, argBytes] at h
  obtain ⟨sp, n, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨sp, (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp n, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact a0
  | 1, _ => exact a1
  | 2, _ => exact a2
  | 3, _ => exact a3
  | 4, _ => exact a4
  | 5, _ => exact a5
  | 6, _ => exact a6
  | 7, _ => exact a7
  | 8, _ => exact a8
  | 9, _ => exact a9

section
variable {s₁ s₂ : State}

theorem Pub.bot_eq (P : Pub s₁ s₂) : bot s₁ = bot s₂ := by simp only [bot, P.sp]
theorem Pub.slot_eq (P : Pub s₁ s₂) (d : Nat) : slot s₁ d = slot s₂ d := by simp only [slot, P.bot_eq]
theorem Pub.ptr (P : Pub s₁ s₂) {i : Nat} (hi : i < 10) : argumentPointer s₁ i = argumentPointer s₂ i := by
  simp only [argumentPointer, P.args i hi]
theorem Pub.wW_eq (P : Pub s₁ s₂) : wW s₁ = wW s₂ := by simp only [wW, P.args 3 (by decide)]
theorem Pub.wsR_eq (P : Pub s₁ s₂) : wsR s₁ = wsR s₂ := by
  simp only [wsR, P.ptr (by decide : 8 < 10), P.args 9 (by decide)]
theorem Pub.pcRd_eq (P : Pub s₁ s₂) : pcRd s₁ = pcRd s₂ := by
  simp only [pcRd, P.ptr (by decide : 2 < 10), P.args 3 (by decide)]
theorem Pub.pcWr_eq (P : Pub s₁ s₂) : pcWr s₁ = pcWr s₂ := by
  simp only [pcWr, P.ptr (by decide : 0 < 10), P.wW_eq, P.wsR_eq, P.slot_eq]
theorem Pub.prRd_eq (P : Pub s₁ s₂) : prRd s₁ = prRd s₂ := by
  simp only [prRd, P.ptr (by decide : 2 < 10), P.ptr (by decide : 4 < 10), P.ptr (by decide : 6 < 10),
    P.args 3 (by decide), P.args 5 (by decide), P.args 7 (by decide)]
theorem Pub.prWr_eq (P : Pub s₁ s₂) : prWr s₁ = prWr s₂ := by
  simp only [prWr, P.ptr (by decide : 0 < 10), P.args 3 (by decide), P.wsR_eq, P.slot_eq]
theorem Pub.pubVal_eq (P : Pub s₁ s₂) (j : Nat) : pubVal s₁ j = pubVal s₂ j := by
  match j with
  | 0 => exact P.args 0 (by decide)
  | 1 => exact P.wW_eq
  | 2 => exact P.args 2 (by decide)
  | 3 => exact P.args 3 (by decide)
  | 4 => exact P.args 8 (by decide)
  | _ + 5 => exact P.args 9 (by decide)
theorem Pub.primesVal_eq (P : Pub s₁ s₂) (j : Nat) : primesVal s₁ j = primesVal s₂ j := by
  match j with
  | 0 => exact P.args 0 (by decide)
  | 1 => exact P.args 3 (by decide)
  | 2 => exact P.args 2 (by decide)
  | 3 => exact P.args 3 (by decide)
  | 4 => exact P.args 2 (by decide)
  | 5 => exact P.args 3 (by decide)
  | 6 => exact P.args 4 (by decide)
  | 7 => exact P.args 5 (by decide)
  | 8 => exact P.args 6 (by decide)
  | 9 => exact P.args 7 (by decide)
  | 10 => exact P.args 4 (by decide)
  | 11 => exact P.args 5 (by decide)
  | 12 => exact P.args 6 (by decide)
  | 13 => exact P.args 7 (by decide)
  | 14 => exact P.args 4 (by decide)
  | 15 => exact P.args 5 (by decide)
  | 16 => exact P.args 8 (by decide)
  | _ + 17 => exact P.args 9 (by decide)

/-- Sequencing, with what each run leaves. -/
theorem seqCT {P : State → State → Prop} {a b : Prog isa} {F₁ F₂ : State → Prop}
    (ha : RelCT isa P a fun _ _ => True) (hw : ∀ x y, P x y → WP isa a x F₁ ∧ WP isa a y F₂)
    (hb : RelCT isa (fun x y => F₁ x ∧ F₂ y) b fun _ _ => True) : RelCT isa P (.seq a b) fun _ _ => True :=
  VG.RelCT.seq (ha.wp hw) (hb.mono (fun _ _ h => h.2) (fun _ _ _ => trivial))

/-- Code that the taint analysis checks with only `esp` public. -/
theorem espCT {P : State → State → Prop} (hP : ∀ x y, P x y → x.gpr .esp = y.gpr .esp) {c : Prog isa}
    (h : (VG.Taint.check taint (τr [.esp]) c (VG.Taint.hintOf taint (τr [.esp]) c)).isSome = true) :
    RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) _ (fun x y hp => agree_regs fun r hr => by
    obtain rfl := List.mem_singleton.mp hr; exact hP x y hp) h

theorem Body.esp (P : Pub s₁ s₂) {x y : State} (B₁ : Body s₁ x) (B₂ : Body s₂ y) : x.gpr .esp = y.gpr .esp := by
  rw [B₁.sp, B₂.sp, P.sp]

theorem pc_pub (A₁ : PPABI s₁) (A₂ : PPABI s₂) (P : Pub s₁ s₂) {u₁ u₂ : State} (B₁ : Body s₁ u₁) (B₂ : Body s₂ u₂)
    (V₁ : ∀ j < 6, u₁.mem.readW (slot s₁ (4 * j)) 32 = pubVal s₁ j)
    (V₂ : ∀ j < 6, u₂.mem.readW (slot s₂ (4 * j)) 32 = pubVal s₂ j) {rd wr : List Region} :
    (Spec.Rsa.publicPrecomputeContract abi 96).pub (u₁.callEntry.withRegions rd wr)
      (u₂.callEntry.withRegions rd wr) := by
  have h₁ : ∀ j < 6, arg (u₁.callEntry.withRegions rd wr) j = pubVal s₁ j := fun j hj => by
    rw [callee_arg A₁ B₁ (by omega)]; exact V₁ j hj
  have h₂ : ∀ j < 6, arg (u₂.callEntry.withRegions rd wr) j = pubVal s₂ j := fun j hj => by
    rw [callee_arg A₂ B₂ (by omega)]; exact V₂ j hj
  have cb₁ := callee_bytes (rd := rd) (wr := wr) A₁ B₁ (n_apart A₁) (arg s₁ 3).isLt
  have cb₂ := callee_bytes (rd := rd) (wr := wr) A₂ B₂ (n_apart A₂) (arg s₂ 3).isLt
  sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argSlots, argVal, argBytes]
  simp only [h₁ 0 (by decide), h₁ 1 (by decide), h₁ 2 (by decide), h₁ 3 (by decide), h₁ 4 (by decide), h₁ 5 (by decide), h₂ 0 (by decide), h₂ 1 (by decide), h₂ 2 (by decide), h₂ 3 (by decide), h₂ 4 (by decide), h₂ 5 (by decide)]
  simp only [State.withRegions_mem, State.callEntry_mem, argumentPointer] at cb₁ cb₂
  refine ⟨by rw [sp4 A₁ B₁, sp4 A₂ B₂, P.sp], ?_, P.pubVal_eq 0, P.pubVal_eq 1, P.pubVal_eq 2, P.pubVal_eq 3,
    P.pubVal_eq 4, P.pubVal_eq 5⟩
  simp only [pubVal]
  rw [cb₁, cb₂]
  exact congrArg _ P.n

theorem pr_pub (A₁ : PPABI s₁) (A₂ : PPABI s₂) (P : Pub s₁ s₂) {u₁ u₂ : State} (B₁ : Body s₁ u₁) (B₂ : Body s₂ u₂)
    (V₁ : ∀ j < 18, u₁.mem.readW (slot s₁ (4 * j)) 32 = primesVal s₁ j)
    (V₂ : ∀ j < 18, u₂.mem.readW (slot s₂ (4 * j)) 32 = primesVal s₂ j) {rd wr : List Region} :
    (Proof.Rsa.privateCrtContract abi 96).pub (u₁.callEntry.withRegions rd wr)
      (u₂.callEntry.withRegions rd wr) := by
  have h₁ : ∀ j < 18, arg (u₁.callEntry.withRegions rd wr) j = primesVal s₁ j := fun j hj => by
    rw [callee_arg A₁ B₁ hj]; exact V₁ j hj
  have h₂ : ∀ j < 18, arg (u₂.callEntry.withRegions rd wr) j = primesVal s₂ j := fun j hj => by
    rw [callee_arg A₂ B₂ hj]; exact V₂ j hj
  have cb₁ := callee_bytes (rd := rd) (wr := wr) A₁ B₁ (n_apart A₁) (arg s₁ 3).isLt
  have cb₂ := callee_bytes (rd := rd) (wr := wr) A₂ B₂ (n_apart A₂) (arg s₂ 3).isLt
  sig_pub [Proof.Rsa.privateCrtContract, Proof.Rsa.privateCrtSig, abi, argSlots, argVal, argBytes]
  simp only [h₁ 0 (by decide), h₁ 1 (by decide), h₁ 2 (by decide), h₁ 3 (by decide), h₁ 4 (by decide), h₁ 5 (by decide), h₁ 6 (by decide), h₁ 7 (by decide), h₁ 8 (by decide), h₁ 9 (by decide), h₁ 10 (by decide), h₁ 11 (by decide), h₁ 12 (by decide), h₁ 13 (by decide), h₁ 14 (by decide), h₁ 15 (by decide), h₁ 16 (by decide), h₁ 17 (by decide), h₂ 0 (by decide), h₂ 1 (by decide), h₂ 2 (by decide), h₂ 3 (by decide), h₂ 4 (by decide), h₂ 5 (by decide), h₂ 6 (by decide), h₂ 7 (by decide), h₂ 8 (by decide), h₂ 9 (by decide), h₂ 10 (by decide), h₂ 11 (by decide), h₂ 12 (by decide), h₂ 13 (by decide), h₂ 14 (by decide), h₂ 15 (by decide), h₂ 16 (by decide), h₂ 17 (by decide)]
  simp only [State.withRegions_mem, State.callEntry_mem, argumentPointer] at cb₁ cb₂
  refine ⟨by rw [sp4 A₁ B₁, sp4 A₂ B₂, P.sp], ?_, P.primesVal_eq 0, P.primesVal_eq 1, P.primesVal_eq 2, P.primesVal_eq 3, P.primesVal_eq 4, P.primesVal_eq 5, P.primesVal_eq 6, P.primesVal_eq 7, P.primesVal_eq 8, P.primesVal_eq 9, P.primesVal_eq 10, P.primesVal_eq 11, P.primesVal_eq 12, P.primesVal_eq 13, P.primesVal_eq 14, P.primesVal_eq 15, P.primesVal_eq 16, P.primesVal_eq 17⟩
  simp only [primesVal]
  rw [cb₁, cb₂]
  exact congrArg _ P.n

/-- `copyPrimes`' first block: `esi` and `ebp` saved in the frame. -/
theorem saves_ok {s t : State} (A : PPABI s) (B : Body s t) :
    WP isa (.block [.store (Impl.Bignum.X86.PrivPre.stackAt Impl.Bignum.X86.PrivPre.saveOffset) .esi,
      .store (Impl.Bignum.X86.PrivPre.stackAt (Impl.Bignum.X86.PrivPre.saveOffset + 4)) .ebp]) t (Body s) :=
  wp_slot A B (d := 88) (by decide) fun _ B₁ _ => wp_slot A B₁ (d := 92) (by decide) fun _ B₂ _ =>
    WP.block_nil B₂

/-- What `copyPrime`'s block leaves. -/
def CB (s : State) (j i : Nat) (skip : Option Nat) (u : State) : Prop :=
  Body s u ∧ Rt.PtrAt u (argumentPointer s 8) .esi (CrtRt.lo (arg s 3).toNat (.slot .wide j)) ∧
    Rt.PtrAt u (argumentPointer s 0) .ebp (dstOff s skip) ∧
    (u.gpr .ecx).toNat = 4 * (2 * Spec.Rsa.primeWords (arg s i).toNat)

theorem copyPrime_relCT (A₁ : PPABI s₁) (A₂ : PPABI s₂) (P : Pub s₁ s₂) {j i : Nat} {skip : Option Nat}
    (hj : j = 16 ∨ j = 17) (hi : i = 5 ∨ i = 7) (hs : skip = none ∨ skip = some 5) :
    RelCT isa (fun x y => Body s₁ x ∧ Body s₂ y) (copyPrime j i skip) fun _ _ => True := by
  unfold copyPrime
  refine seqCT (F₁ := CB s₁ j i skip) (F₂ := CB s₂ j i skip) (espCT (fun x y h => Body.esp P h.1 h.2) (by
      rcases hj with rfl | rfl <;> rcases hi with rfl | rfl <;> rcases hs with rfl | rfl <;> taint_decide))
    (fun x y h => ⟨WP.mono (copyBlock_ok A₁ h.1 (j := j) hi hs) fun _ ⟨B, _, _, S, E, C⟩ => ⟨B, S, E, C⟩,
      WP.mono (copyBlock_ok A₂ h.2 (j := j) hi hs) fun _ ⟨B, _, _, S, E, C⟩ => ⟨B, S, E, C⟩⟩) ?_
  refine RelCT.taint (A := taint) (τr [.esp, .esi, .ebp, .ecx])
    (fun x y ⟨⟨Bx, Sx, Ex, Cx⟩, ⟨By, Sy, Ey, Cy⟩⟩ => agree_regs fun r hr => ?_) (by taint_decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Body.esp P Bx By
  · apply BitVec.eq_of_toNat_eq
    rw [Sx, Sy, P.ptr (by decide), P.args 3 (by decide)]
  · apply BitVec.eq_of_toNat_eq
    rw [Ex, Ey, P.ptr (by decide)]
    rcases hs with rfl | rfl
    · simp only [dstOff, P.args 3 (by decide)]
    · simp only [dstOff, P.args 3 (by decide), P.args 5 (by decide)]
  · apply BitVec.eq_of_toNat_eq
    rw [Cx, Cy]
    rcases hi with rfl | rfl
    · rw [P.args 5 (by decide)]
    · rw [P.args 7 (by decide)]

theorem copyPrimes_relCT (A₁ : PPABI s₁) (A₂ : PPABI s₂) (P : Pub s₁ s₂) :
    RelCT isa (fun x y => Body s₁ x ∧ Body s₂ y) copyPrimes fun _ _ => True := by
  have parts₁ := pre_parts A₁
  have parts₂ := pre_parts A₂
  unfold copyPrimes
  refine seqCT (espCT (fun x y h => Body.esp P h.1 h.2) (by taint_decide))
    (fun x y h => ⟨saves_ok A₁ h.1, saves_ok A₂ h.2⟩) ?_
  refine seqCT (copyPrime_relCT A₁ A₂ P (j := 16) (.inl rfl) (.inl rfl) (.inl rfl))
    (fun x y h => ⟨WP.mono (copyPrime_ok A₁ h.1 (j := 16) (by decide) (.inl rfl) (.inl rfl)
        (by simp only [dstOff] at parts₁ ⊢; omega)) fun _ h => h.1,
      WP.mono (copyPrime_ok A₂ h.2 (j := 16) (by decide) (.inl rfl) (.inl rfl)
        (by simp only [dstOff] at parts₂ ⊢; omega)) fun _ h => h.1⟩) ?_
  refine seqCT (copyPrime_relCT A₁ A₂ P (j := 17) (.inr rfl) (.inr rfl) (.inr rfl))
    (fun x y h => ⟨WP.mono (copyPrime_ok A₁ h.1 (j := 17) (by decide) (.inr rfl) (.inr rfl) (by omega))
        fun _ h => h.1,
      WP.mono (copyPrime_ok A₂ h.2 (j := 17) (by decide) (.inr rfl) (.inr rfl) (by omega)) fun _ h => h.1⟩) ?_
  exact espCT (fun x y h => Body.esp P h.1 h.2) (by taint_decide)

theorem wrapBody_relCT {pcName prName : String} {pc : Prog isa}
    (pv : Verified target pc (Spec.Rsa.publicPrecomputeContract abi 96)) (pst : stackUse pc ≤ 96) (pns : NoSp pc)
    (prst : stackUse primes ≤ 96) (prns : NoSp primes)
    (A₁ : PPABI s₁) (A₂ : PPABI s₂) (P : Pub s₁ s₂) :
    RelCT isa (fun x y => x = allocFrame Impl.Bignum.X86.PrivPre.frameBytes s₁ ∧
      y = allocFrame Impl.Bignum.X86.PrivPre.frameBytes s₂) (body pcName pc prName primes) fun _ _ => True := by
  unfold body
  -- the callee's arguments of `vg_rsa_public_precompute`
  refine seqCT (F₁ := fun u => Body s₁ u ∧ ∀ j < 6, u.mem.readW (slot s₁ (4 * j)) 32 = pubVal s₁ j)
    (F₂ := fun u => Body s₂ u ∧ ∀ j < 6, u.mem.readW (slot s₂ (4 * j)) 32 = pubVal s₂ j)
    (espCT (fun x y ⟨hx, hy⟩ => by subst hx hy; simp only [allocFrame_esp, P.sp]) (by taint_decide))
    (fun x y ⟨hx, hy⟩ => by
      subst hx hy
      exact ⟨WP.mono (publicArgs_ok A₁ Body.start) fun _ ⟨B, _, _, V⟩ => ⟨B, V⟩,
        WP.mono (publicArgs_ok A₂ Body.start) fun _ ⟨B, _, _, V⟩ => ⟨B, V⟩⟩) ?_
  -- the call of `vg_rsa_public_precompute`
  refine seqCT (F₁ := Body s₁) (F₂ := Body s₂)
    (RelCT.call pv.1 pv.2.1 (pcRd s₁) (pcWr s₁) fun x y ⟨⟨Bx, Vx⟩, ⟨By, Vy⟩⟩ => ?_)
    (fun x y ⟨⟨Bx, Vx⟩, ⟨By, Vy⟩⟩ => ⟨WP.mono (pc_call pv pst pns A₁ Bx Vx) fun _ h => h.1,
      WP.mono (pc_call pv pst pns A₂ By Vy) fun _ h => h.1⟩) ?_
  · rw [P.pcRd_eq, P.pcWr_eq]
    exact ⟨by rw [← P.pcRd_eq, ← P.pcWr_eq]; exact pc_pre A₁ Bx Vx, pc_pre A₂ By Vy,
      pc_pub A₁ A₂ P Bx By Vx Vy, by rw [← P.pcRd_eq, ← P.pcWr_eq]; exact (pc_covers A₁ Bx).1,
      by rw [← P.pcWr_eq]; exact (pc_covers A₁ Bx).2, (pc_covers A₂ By).1, (pc_covers A₂ By).2,
      Body.esp P Bx By⟩
  -- `primes`' arguments
  refine seqCT (F₁ := fun u => Body s₁ u ∧ ∀ j < 18, u.mem.readW (slot s₁ (4 * j)) 32 = primesVal s₁ j)
    (F₂ := fun u => Body s₂ u ∧ ∀ j < 18, u.mem.readW (slot s₂ (4 * j)) 32 = primesVal s₂ j)
    (espCT (fun x y h => Body.esp P h.1 h.2) (by taint_decide))
    (fun x y h => ⟨WP.mono (primesArgs_ok A₁ h.1) fun _ ⟨B, _, _, _, V⟩ => ⟨B, V⟩,
      WP.mono (primesArgs_ok A₂ h.2) fun _ ⟨B, _, _, _, V⟩ => ⟨B, V⟩⟩) ?_
  -- the call of `primes`
  refine seqCT (F₁ := Body s₁) (F₂ := Body s₂)
    (RelCT.call primes_verified.1 primes_verified.2.1 (prRd s₁) (prWr s₁) fun x y ⟨⟨Bx, Vx⟩, ⟨By, Vy⟩⟩ => ?_)
    (fun x y ⟨⟨Bx, Vx⟩, ⟨By, Vy⟩⟩ => ⟨WP.mono (pr_call prst prns A₁ Bx Vx) fun _ h => h.1,
      WP.mono (pr_call prst prns A₂ By Vy) fun _ h => h.1⟩) ?_
  · exact ⟨pr_pre A₁ Bx Vx, by rw [P.prRd_eq, P.prWr_eq]; exact pr_pre A₂ By Vy,
      pr_pub A₁ A₂ P Bx By Vx Vy, (pr_covers A₁ Bx).1, (pr_covers A₁ Bx).2,
      by rw [P.prRd_eq, P.prWr_eq]; exact (pr_covers A₂ By).1, by rw [P.prWr_eq]; exact (pr_covers A₂ By).2,
      Body.esp P Bx By⟩
  -- the result, the copies, and the mask
  refine seqCT (F₁ := Body s₁) (F₂ := Body s₂) (espCT (fun x y h => Body.esp P h.1 h.2) (by taint_decide))
    (fun x y h => ⟨WP.mono (status_ok A₁ h.1) fun _ h => h.1, WP.mono (status_ok A₂ h.2) fun _ h => h.1⟩) ?_
  refine seqCT (F₁ := Body s₁) (F₂ := Body s₂) (copyPrimes_relCT A₁ A₂ P)
    (fun x y h => ⟨WP.mono (copyPrimes_ok A₁ h.1) fun _ h => h.1, WP.mono (copyPrimes_ok A₂ h.2) fun _ h => h.1⟩) ?_
  refine seqCT (F₁ := fun u => Body s₁ u ∧ u.gpr .edx = arg s₁ 0 ∧ (u.gpr .ecx).toNat = (arg s₁ 1).toNat * 8)
    (F₂ := fun u => Body s₂ u ∧ u.gpr .edx = arg s₂ 0 ∧ (u.gpr .ecx).toNat = (arg s₂ 1).toNat * 8)
    (espCT (fun x y h => Body.esp P h.1 h.2) (by taint_decide))
    (fun x y h => ⟨WP.mono (maskArgs_ok A₁ h.1) fun _ ⟨B, _, _, _, D, C⟩ => ⟨B, D, C⟩,
      WP.mono (maskArgs_ok A₂ h.2) fun _ ⟨B, _, _, _, D, C⟩ => ⟨B, D, C⟩⟩) ?_
  refine seqCT (F₁ := Body s₁) (F₂ := Body s₂)
    (RelCT.taint (A := taint) (τr [.esp, .edx, .ecx])
      (fun x y ⟨⟨Bx, Dx, Cx⟩, ⟨By, Dy, Cy⟩⟩ => agree_regs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Body.esp P Bx By
        · rw [Dx, Dy, P.args 0 (by decide)]
        · exact BitVec.eq_of_toNat_eq (by rw [Cx, Cy, P.args 1 (by decide)])) (by taint_decide))
    (fun x y ⟨⟨Bx, Dx, Cx⟩, ⟨By, Dy, Cy⟩⟩ => ⟨WP.mono (maskLoop_ok A₁ Bx Dx Cx) fun _ h => h.1,
      WP.mono (maskLoop_ok A₂ By Dy Cy) fun _ h => h.1⟩) ?_
  exact espCT (fun x y h => Body.esp P h.1 h.2) (by taint_decide)

end
end VG.Proof.Bignum.X86.PrivPre
