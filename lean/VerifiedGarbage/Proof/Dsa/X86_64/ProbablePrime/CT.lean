module

public import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Body
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytesCT
import VerifiedGarbage.Proof.Framework.X86_64.FrameAlloc
public meta import VerifiedGarbage.Proof.Dsa.X86_64.ProbablePrime.Body
public meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PrimeBytesCT
public meta import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.MontMul
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.BitLengthBounds
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract

/-! # The probable-prime test's timing depends only on its public inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.ProbablePrime
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64

/-- What the contract makes public: the arguments, the size among them, the
stack pointer, the candidate and the tape. -/
structure View where
  rdi : Addr
  rsi : Addr
  rdx : Addr
  rcx : Addr
  r8 : Addr
  r9 : Addr
  rsp : Addr
  N : Nat
  rand : List Byte

def view (s : State) : View :=
  ⟨s.gpr .rdi, s.gpr .rsi, s.gpr .rdx, s.gpr .rcx, s.gpr .r8, s.gpr .r9, s.gpr .rsp,
    candidateOf (s.gpr .r9).toNat s, Spec.Rsa.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat⟩

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem view_of_pub {s₁ s₂ : State} (h : contract.pub s₁ s₂) : view s₁ = view s₂ := by
  sig_pub [contract, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi,
    argRegs] at h
  obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9⟩ := h
  obtain ⟨-, hl⟩ := List.cons.inj hl
  obtain ⟨hN, hr⟩ := List.cons.inj hl
  have hr' := map_toNat_inj hr
  unfold view candidateOf
  rw [hN, hr', hsp, hdi, hsi, hdx, hcx, h8, h9]

/-- Big-endian octet strings of one length are equal if their values are. -/
theorem os2ip_inj : ∀ {l₁ l₂ : List Byte}, l₁.length = l₂.length →
    Spec.Rsa.os2ip l₁ = Spec.Rsa.os2ip l₂ → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [os2ip_cons, os2ip_cons, hl] at h
    have h₁ := os2ip_lt l₁
    have h₂ := os2ip_lt l₂
    rw [hl] at h₁
    have hd : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) / 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) / 256 ^ l₂.length := by rw [h]
    have hm : (a.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₁) % 256 ^ l₂.length =
        (b.toNat * 256 ^ l₂.length + Spec.Rsa.os2ip l₂) % 256 ^ l₂.length := by rw [h]
    have hp : 0 < 256 ^ l₂.length := Nat.pow_pos (by decide)
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₁, Nat.zero_add,
      Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt h₂, Nat.zero_add] at hd
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₁,
      Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h₂] at hm
    rw [BitVec.eq_of_toNat_eq hd, os2ip_inj hl hm]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

open VG.Impl.Dsa.X86_64.ProbablePrime VG.Impl.Dsa.Generation.Layout VG.Impl.RsaKeyGen.X86_64.Candidate
open VG.Proof.MillerRabin.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Dsa.X86_64.Generation (PrimeParams PrimeCallPublic PrimeBytesPublic PrimeBytesBefore
  CalleeHeaderLayout DrawPublic)

theorem params_ext {P Q : PrimeParams} (hB : P.B = Q.B) (hp : P.p = Q.p) (hrp : P.rp = Q.rp)
    (hsp : P.sp = Q.sp) (hZ : P.Z = Q.Z) (hw : P.w = Q.w) (hN : P.N = Q.N) (hlen : P.len = Q.len)
    (hd : P.drawBytes = Q.drawBytes) (hc : P.checks = Q.checks) (hr : P.rand = Q.rand) : P = Q := by
  cases P; cases Q
  simp only at hB hp hrp hsp hZ hw hN hlen hd hc hr
  subst hB hp hrp hsp hZ hw hN hlen hd hc hr
  rfl

/-- The test's public parameters, as the generation's timing lemmas take them. -/
def callPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeCallPublic where
  draw := ⟨params hb A, 0⟩
  arena := s.gpr .rdi
  wr := (allocState 56 s).wr
  layout := by
    right
    have hw : (allocState 56 s).wr = [⟨frameSp s, 56⟩, wsRegion s, ⟨s.gpr .r8, 8⟩] := by
      change ⟨frameSp s, 56⟩ :: s.wr = _; rw [A.wr]
    rw [hw]
    refine ⟨⟨frameSp s, 56⟩, ⟨s.gpr .r8, 8⟩, (s.gpr .rsi).toNat * 8, rfl,
      by have := A.size; have : domainCheck = 40960 := rfl; omega, ?_, ?_⟩
    · have hs := frame_stack_sub s (d := 0) (n := 56) (by decide)
      simp only [off, BitVec.add_zero] at hs
      refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact A.stackWs.sub_left hs
        · exact A.stackUsed.sub_left hs
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact A.wsUsed
      · intro r hr; cases hr
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (by decide : (56 : Nat) ≤ 2 ^ 64)
      · have := A.wsBound; change (s.gpr .rsi).toNat * 8 ≤ 2 ^ 64; omega
      · exact (by decide : (8 : Nat) ≤ 2 ^ 64)
  base := rfl
  width := by change words bits ≤ 48; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  tab := by
    change Bignum.slot (words bits) aTab + 2048 ≤ arithmeticBytes
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  large := by
    change 8161 < candidateOf bits s
    have hlow := ((bitLength_iff_bounds (by have := hb.le; omega)).mp A.bits).1
    have h2 : 2 ^ 159 ≤ 2 ^ (bits - 1) := Nat.pow_le_pow_right (by decide) (by have := hb.le; omega)
    have : (8161 : Nat) < 2 ^ 159 := by decide
    exact Nat.lt_of_lt_of_le this (Nat.le_trans h2 hlow)
  policy := by
    change 1024 < Spec.Dsa.bitLength (candidateOf bits s) ↔ 16 < words bits
    rw [A.bits]; rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide

def bytesPublic {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) : PrimeBytesPublic where
  call := callPublic hb A
  source := off (s.gpr .rdi) (candidate bits)
  bytes := Spec.Rsa.bytesAt s.mem (off (s.gpr .rdi) (candidate bits)) (len bits)
  length := bytesAt_length _ _ _
  value := rfl

theorem PrimeABI.toNat_r9 {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) :
    (s.gpr .r9).toNat = bits := by
  rw [A.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hb.le; omega)]

theorem bytesPublic_eq {bits : Nat} (hb : Supported bits) {s₁ s₂ : State} (A₁ : PrimeABI bits s₁)
    (A₂ : PrimeABI bits s₂) (hv : view s₁ = view s₂) : bytesPublic hb A₁ = bytesPublic hb A₂ := by
  simp only [view, View.mk.injEq, A₁.toNat_r9 hb, A₂.toNat_r9 hb] at hv
  obtain ⟨hdi, hsi, hdx, hcx, h8, -, hsp, hN, hr⟩ := hv
  have hP : params hb A₁ = params hb A₂ :=
    params_ext (by simp only [params, hdi]) (by simp only [params, hdi]) hdx (by simp only [params, frameSp, hsp])
      rfl rfl hN rfl rfl rfl hr
  have hwr : (allocState 56 s₁).wr = (allocState 56 s₂).wr := by
    change ⟨frameSp s₁, 56⟩ :: s₁.wr = ⟨frameSp s₂, 56⟩ :: s₂.wr
    rw [A₁.wr, A₂.wr, frameSp, frameSp, hsp, hdi, hsi, h8]
  have hbytes : Spec.Rsa.bytesAt s₁.mem (off (s₁.gpr .rdi) (candidate bits)) (len bits) =
      Spec.Rsa.bytesAt s₂.mem (off (s₂.gpr .rdi) (candidate bits)) (len bits) :=
    os2ip_inj (by rw [bytesAt_length, bytesAt_length]) hN
  rw [hdi] at hbytes
  unfold bytesPublic callPublic
  simp only [hP, hwr, hdi, hbytes]

theorem before_of_ready {bits : Nat} (hb : Supported bits) {s : State} (A : PrimeABI bits s) {u : State}
    (R : Ready hb A u) : PrimeBytesBefore (len bits) (draw bits) (bytesPublic hb A) u :=
  ⟨⟨0, R.args⟩, R.ptr, R.src, R.wr, Nat.zero_le _, rfl, rfl⟩

/-! ## The stages, each with the public view of the arguments -/

def Entered (v : View) (u : State) : Prop :=
  ∃ s, ∃ _ : Supported v.r9.toNat, ∃ _ : PrimeABI v.r9.toNat s, view s = v ∧ u = allocState 56 s

def ReadyAt (v : View) (u : State) : Prop :=
  ∃ s, ∃ hb : Supported v.r9.toNat, ∃ A : PrimeABI v.r9.toNat s, view s = v ∧ Ready hb A u

def TestedAt (v : View) (u : State) : Prop :=
  ∃ s, ∃ hb : Supported v.r9.toNat, ∃ A : PrimeABI v.r9.toNat s, view s = v ∧ Tested hb A u

/-- The workspace, the stack pointer and `used` in their registers. -/
def Loaded (v : View) (u : State) : Prop :=
  u.gpr .rdi = off v.rdi arithmetic ∧ u.gpr .rsp = v.rsp - BitVec.ofNat 64 56 ∧ u.gpr .r8 = v.r8

theorem post_of_exec {c : Prog isa} {s t : State} {trace : List Leak} {Q : State → Prop}
    (h : WP isa c s Q) (he : Exec isa c s trace t) : Q t := by
  obtain ⟨_, u, hu, hq⟩ := h
  obtain ⟨_, heq⟩ := Exec.det he hu
  rw [heq]
  exact hq

theorem setup_ct : RelCT isa (Two Entered) setup (Two ReadyAt) := by
  have pins : Pins Entered [.rdi, .rsp, .r9] := by
    rintro v u₁ u₂ ⟨s₁, -, -, h₁, rfl⟩ ⟨s₂, -, -, h₂, rfl⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    have h := h₁.trans h₂.symm
    simp only [view, View.mk.injEq] at h
    rcases hr with rfl | rfl | rfl
    · simp [allocState, State.setReg, h.1]
    · simp [allocState, State.setReg, h.2.2.2.2.2.2.1]
    · simp [allocState, State.setReg, h.2.2.2.2.2.1]
  refine two_post (two_taint [.rdi, .rsp, .r9] pins (by taint_decide))
    fun v u ⟨s, hb, A, hv, hu⟩ => hu ▸ WP.mono (prep_ok hb A) fun t R => ⟨s, hb, A, hv, R⟩

theorem test_ct (M : Mont) (K : Kernel) :
    RelCT isa (Two ReadyAt) (Impl.Dsa.X86_64.Generation.primeBytes M.mm K.run) (Two TestedAt) := by
  rintro u₁ u₂ t₁ t₂ u₁' u₂' ⟨v, ⟨s₁, hb, A₁, hv₁, R₁⟩, ⟨s₂, _, A₂, hv₂, R₂⟩⟩ e₁ e₂
  have hct := VG.Proof.Dsa.X86_64.Generation.primeBytes_ct M K (len v.r9.toNat) (draw v.r9.toNat)
  have hp₂ : PrimeBytesBefore (len v.r9.toNat) (draw v.r9.toNat) (bytesPublic hb A₁) u₂ := by
    rw [bytesPublic_eq hb A₁ A₂ (hv₁.trans hv₂.symm)]; exact before_of_ready hb A₂ R₂
  exact ⟨(hct _ _ _ _ _ _ ⟨_, before_of_ready hb A₁ R₁, hp₂⟩ e₁ e₂).1, v,
    ⟨s₁, hb, A₁, hv₁, post_of_exec (test_ok M K hb A₁ R₁) e₁⟩,
    ⟨s₂, hb, A₂, hv₂, post_of_exec (test_ok M K hb A₂ R₂) e₂⟩⟩

/-- The exit's loads of the workspace's word and of `used`. -/
abbrev exitLoad : List Instr :=
  [.mov .rax (.mem (Impl.Bignum.X86_64.hdr kUsed)), .mov .r8 (.mem (sp 48))]

abbrev exitStatus : List Instr :=
  [.store { base := .r8 } .rax, .mov .rax (.mem (Impl.Bignum.X86_64.hdr kStat)), .mov .rcx (.reg .rax),
    .shift .shr .rcx 1, .alu .sub .rax (.reg .rcx)]

theorem tested_regs {bits : Nat} {hb : Supported bits} {s u : State} {A : PrimeABI bits s}
    (T : Tested hb A u) : u.gpr .rdi = off (s.gpr .rdi) arithmetic ∧ u.gpr .rsp = frameSp s := by
  obtain ⟨⟨_, _, inp, _⟩, _⟩ := T
  exact ⟨inp.good.rdi, inp.stack⟩

theorem load_ok {v : View} {u : State} (h : TestedAt v u) :
    WP isa (.block exitLoad) u (Loaded v) := by
  obtain ⟨s, hb, A, rfl, T⟩ := h
  obtain ⟨hdi, hsp⟩ := tested_regs T
  obtain ⟨⟨_, _, inp, _⟩, _, hu, _, _, hwr⟩ := T
  have h200 := inp.good.scr.ld (d := 200) (by change _ ≤ arithmeticBytes; decide)
  have h48 : InRegions (u.rd ++ u.wr) (off (frameSp s) 48) 8 :=
    ⟨_, List.mem_append_right _ (by rw [hwr]; exact List.mem_cons_self),
      Offset.contains_base _ (by decide) (by decide)⟩
  refine WP.mono (WP.keep [.rax, .r8] (Q := fun t => t.gpr .r8 = s.gpr .r8) (by
    xrun [exitLoad, sp, State.ea, BitVec.ofInt_natCast, Impl.Bignum.X86_64.hdr, inp.good.rdi, kUsed,
      VG.Impl.Bignum.sFn, hdrOff, Nat.reduceAdd, Nat.reduceMul, h200, hsp, h48]
    exact hu) rfl) fun t ⟨h8, hk⟩ => ?_
  exact ⟨(hk.gpr (by decide)).trans hdi, (hk.gpr (by decide)).trans hsp, h8⟩

theorem finish_ct :
    RelCT isa (Two TestedAt) (.seq (.block exit) (.block restoreRegisters)) fun _ _ => True := by
  have pins : Pins TestedAt [.rdi, .rsp] := by
    rintro v u₁ u₂ ⟨s₁, _, A₁, h₁, T₁⟩ ⟨s₂, _, A₂, h₂, T₂⟩ r hr
    have h := h₁.trans h₂.symm
    simp only [view, View.mk.injEq] at h
    obtain ⟨d₁, p₁⟩ := tested_regs T₁
    obtain ⟨d₂, p₂⟩ := tested_regs T₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [d₁, d₂, h.1]
    · rw [p₁, p₂, frameSp, frameSp, h.2.2.2.2.2.2.1]
  refine RelCT.seq (R := fun (a b : State) => ∀ r ∈ [Reg.rsp], a.gpr r = b.gpr r) ?_ ?_
  · change RelCT isa _ (.block (exitLoad ++ exitStatus)) _
    refine RelCT.block_append (RelCT.seq
      (two_post (two_taint [.rdi, .rsp] pins (by taint_decide)) fun v u h => load_ok h) ?_)
    refine RelCT.taintRegs (τ := Taint.ofRegs [.rdi, .rsp, .r8]) (fun x y ⟨v, h₁, h₂⟩ => Taint.agree_ofRegs ?_)
      [.rsp] (by taint_decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h₁.1, h₂.1]
    · rw [h₁.2.1, h₂.2.1]
    · rw [h₁.2.2, h₂.2.2]
  · exact RelCT.mono (RelCT.taintRegs (τ := Taint.ofRegs [.rsp]) (fun x y h => Taint.agree_ofRegs h) []
      (by taint_decide)) (fun _ _ h => h) fun _ _ _ => trivial

theorem code_ct (M : Mont) (K : Kernel) :
    ConstantTime isa contract.pre contract.pub (code M.mm K.run) := by
  refine RelCT.constantTime (Q := fun _ _ => True) (RelCT.alloc (R := fun _ _ => True) ?_)
  refine RelCT.mono (RelCT.seq setup_ct (RelCT.seq (test_ct M K) finish_ct)) ?_ fun _ _ h => h
  rintro a b ⟨s₁, s₂, ⟨h₁, h₂, hp⟩, rfl, rfl⟩
  have hv := view_of_pub hp
  have h9 : s₂.gpr .r9 = s₁.gpr .r9 := by
    simp only [view, View.mk.injEq] at hv; exact hv.2.2.2.2.2.1.symm
  obtain ⟨hb₁, A₁⟩ := primeABI_of h₁
  obtain ⟨-, A₂⟩ := primeABI_of h₂
  rw [h9] at A₂
  exact ⟨view s₁, ⟨s₁, hb₁, A₁, rfl, rfl⟩, ⟨s₂, hb₁, A₂, hv.symm, rfl⟩⟩

end VG.Proof.Dsa.X86_64.ProbablePrime
