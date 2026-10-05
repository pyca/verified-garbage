import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Hint
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.MlDsa.Pack.Hint2
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.MemTaint`. -/
section

/-!
# Taint tracking over memory both runs agree on (x86-64)

The x86-64 counterpart of ML-KEM's AArch64 `memTaint`
(`Proof/MlKem/AArch64/MemTaint.lean`).

The taint analysis (`Proof/Framework/X86_64/Taint.lean`) treats memory as
secret. `memTaint` is one for code that runs from states whose permitted
memory both runs agree on (`MemEq`): every byte load (`movzx8`) and 32-bit
load (`mov32` from memory) it makes is then public, and a byte or 32-bit
store keeps the agreement if it stores a public value at a public address.
It proves constant time for code whose branches and addresses depend on the
contents of such memory: `vg_mldsa_hint_bit_pack` and
`vg_mldsa_hint_bit_unpack`, which may leak their input (the only memory
they read) once they have zeroed their output (the only memory they
write).
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64
open VG.X86_64.Taint (T pub dstOf exec_nonstore memPub)

/-- `m₁` and `m₂` agree on every byte of the regions `rs`. -/
def MemEq (rs : List Region) (m₁ m₂ : Mem) : Prop := ∀ x, InRegions rs x 1 → m₁ x = m₂ x

/-- The registers `τ` agree, and the permissions and the memory they permit. -/
def MAgree (τ : VG.X86_64.Taint.T) (s₁ s₂ : VG.X86_64.State) : Prop :=
  X86_64.Taint.Agree τ s₁ s₂ ∧ s₁.rd = s₂.rd ∧ s₁.wr = s₂.wr ∧ VG.Proof.MlDsa.X86_64.Pack.MemEq (s₁.rd ++ s₁.wr) s₁.mem s₂.mem

/-- The loads whose value the analysis makes public, and the register they
write. -/
def loadDst : Instr → Option Reg
  | .movzx8 d _ => some d
  | .mov32 d (.mem _) => some d
  | _ => none

/-- Loads are public; byte and 32-bit stores must store public values; other
instructions that write memory are not analysed. -/
def mstep (τ : VG.X86_64.Taint.T) (i : Instr) : Option VG.X86_64.Taint.T :=
  match VG.Proof.MlDsa.X86_64.Pack.loadDst i with
  | some d => (X86_64.Taint.step τ i).map fun τ' => { τ' with regs := τ'.regs.insert d }
  | none => match i with
    | .store8 _ r | .store32 _ r => if pub τ r then X86_64.Taint.step τ i else none
    | _ => if (dstOf i).isSome then X86_64.Taint.step τ i else none

theorem MemEq.read {rs : List Region} {m₁ m₂ : Mem} (h : VG.Proof.MlDsa.X86_64.Pack.MemEq rs m₁ m₂) {a : Addr} {n : Nat}
    (hi : InRegions rs a n) (hn : n < 2 ^ 64) : m₁.read a n = m₂.read a n := by
  obtain ⟨r, hr, hc⟩ := hi
  exact Mem.read_congr fun i hi' =>
    h _ ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hi')⟩

theorem MemEq.writeW {rs : List Region} {m₁ m₂ : Mem} (h : VG.Proof.MlDsa.X86_64.Pack.MemEq rs m₁ m₂) (a : Addr) {w : Nat}
    (v : BitVec w) : VG.Proof.MlDsa.X86_64.Pack.MemEq rs (m₁.writeW a v) (m₂.writeW a v) := fun x hx => by
  simp only [Mem.writeW, Mem.write]
  split
  · rfl
  · exact h x hx

/-- A register made public, whose values agree. -/
theorem agree_insert {τ : VG.X86_64.Taint.T} {s₁ s₂ : VG.X86_64.State} (ha : X86_64.Taint.Agree τ s₁ s₂) {d : Reg}
    (hd : s₁.gpr d = s₂.gpr d) : X86_64.Taint.Agree { τ with regs := τ.regs.insert d } s₁ s₂ :=
  ⟨⟨fun r hr => by
      rcases RegSet.mem_insert.mp hr with rfl | hr
      · exact hd
      · exact ha.rf.1 r hr, ha.rf.2⟩, ha.wr, ha.wf₁, ha.wf₂, ha.ok, ha.slots, ha.lo⟩

theorem memPub_of_step {τ τ' : VG.X86_64.Taint.T} {i : Instr} {d : Reg} {m : MemOp}
    (hi : i = .movzx8 d m ∨ i = .mov32 d (.mem m)) (hs : X86_64.Taint.step τ i = some τ') :
    memPub τ m = true := by
  cases hmp : memPub τ m
  · rcases hi with rfl | rfl <;> simp [X86_64.Taint.step, X86_64.Taint.srcOk, hmp] at hs
  · rfl

theorem mstep_sound {τ τ' : VG.X86_64.Taint.T} {i : Instr} {s₁ s₂ s₁' s₂' : VG.X86_64.State} (ha : VG.Proof.MlDsa.X86_64.Pack.MAgree τ s₁ s₂)
    (hs : VG.Proof.MlDsa.X86_64.Pack.mstep τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Proof.MlDsa.X86_64.Pack.MAgree τ' s₁' s₂' := by
  unfold VG.Proof.MlDsa.X86_64.Pack.mstep at hs
  split at hs
  · -- A load.
    rename_i d hd
    obtain ⟨τ₀, h₀, rfl⟩ := Option.map_eq_some_iff.mp hs
    obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 h₀ e₁ e₂
    have hdst : dstOf i = some d := by
      cases i <;> simp only [VG.Proof.MlDsa.X86_64.Pack.loadDst, reduceCtorEq] at hd
      · rename_i src; cases src <;> simp only [reduceCtorEq, Option.some.injEq] at hd; subst hd; rfl
      · simp only [Option.some.injEq] at hd; subst hd; rfl
    obtain ⟨r₁, w₁, m₁, -⟩ := exec_nonstore hdst e₁
    obtain ⟨r₂, w₂, m₂, -⟩ := exec_nonstore hdst e₂
    refine ⟨hadd, VG.Proof.MlDsa.X86_64.Pack.agree_insert ht ?_, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
      rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩
    cases i <;> simp only [VG.Proof.MlDsa.X86_64.Pack.loadDst, reduceCtorEq] at hd
    · rename_i d' src
      cases src <;> simp only [reduceCtorEq, Option.some.injEq] at hd
      subst hd
      rename_i m
      have hm := VG.Proof.MlDsa.X86_64.Pack.memPub_of_step (.inr rfl) h₀
      have ea := ha.1.ea hm
      simp only [exec, readSrc32, State.load32, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨v₁, l₁, rfl⟩ := e₁; obtain ⟨v₂, l₂, rfl⟩ := e₂
      split at l₁ <;> [rename_i hi; cases l₁]
      split at l₂ <;> [skip; cases l₂]
      cases l₁; cases l₂
      simp only [State.setReg32, State.setReg, ite_true, Mem.readW, ← ea, ha.2.2.2.read hi (by decide)]
    · rename_i m
      simp only [Option.some.injEq] at hd; subst hd
      have hm := VG.Proof.MlDsa.X86_64.Pack.memPub_of_step (.inl rfl) h₀
      have ea := ha.1.ea hm
      simp only [exec, State.load8, Option.map_eq_some_iff] at e₁ e₂
      obtain ⟨v₁, l₁, rfl⟩ := e₁; obtain ⟨v₂, l₂, rfl⟩ := e₂
      split at l₁ <;> [rename_i hi; cases l₁]
      split at l₂ <;> [skip; cases l₂]
      cases l₁; cases l₂
      simp only [State.setReg, ite_true, ← ea, ha.2.2.2 _ hi]
  · split at hs
    · -- A store.
      rename_i m r _
      split at hs <;> [rename_i hr; cases hs]
      obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 hs e₁ e₂
      have hm : memPub τ m = true := by
        cases hmp : memPub τ m
        · simp [X86_64.Taint.step, X86_64.Taint.storeStep, hmp] at hs
        · rfl
      have ea := ha.1.ea hm
      simp only [exec, State.store8] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      refine ⟨hadd, ht, ha.2.1, ha.2.2.1, ?_⟩
      rw [ea, ha.1.reg hr]
      exact ha.2.2.2.writeW _ _
    · rename_i m r _
      split at hs <;> [rename_i hr; cases hs]
      obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 hs e₁ e₂
      have hm : memPub τ m = true := by
        cases hmp : memPub τ m
        · simp [X86_64.Taint.step, X86_64.Taint.storeStep, hmp] at hs
        · rfl
      have ea := ha.1.ea hm
      simp only [exec, State.store32] at e₁ e₂
      split at e₁ <;> [skip; cases e₁]
      split at e₂ <;> [skip; cases e₂]
      cases e₁; cases e₂
      refine ⟨hadd, ht, ha.2.1, ha.2.2.1, ?_⟩
      rw [ea, ha.1.reg hr]
      exact ha.2.2.2.writeW _ _
    · -- An instruction that writes one register.
      split at hs <;> [rename_i hd; cases hs]
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hd
      obtain ⟨hadd, ht⟩ := X86_64.Taint.step_sound ha.1 hs e₁ e₂
      obtain ⟨r₁, w₁, m₁, -⟩ := exec_nonstore hd e₁
      obtain ⟨r₂, w₂, m₂, -⟩ := exec_nonstore hd e₂
      exact ⟨hadd, ht, by rw [r₁, r₂, ha.2.1], by rw [w₁, w₂, ha.2.2.1], by
        rw [m₁, m₂, r₁, w₁]; exact ha.2.2.2⟩

/-- Taint tracking over memory both runs agree on, for x86-64. -/
def memTaint : VG.Taint isa where
  T := VG.X86_64.Taint.T
  Agree := VG.Proof.MlDsa.X86_64.Pack.MAgree
  step := VG.Proof.MlDsa.X86_64.Pack.mstep
  step_sound := VG.Proof.MlDsa.X86_64.Pack.mstep_sound
  condPub τ _ := τ.flags
  cond_sound ha hc := X86_64.Taint.cond_sound ha.1 hc
  meet := X86_64.Taint.meet
  meet_left h := ⟨X86_64.Taint.meet_left h.1, h.2⟩
  meet_right h := ⟨X86_64.Taint.meet_right h.1, h.2⟩
  le := X86_64.Taint.leK
  le_sound hle h := ⟨X86_64.Taint.le_sound (X86_64.Taint.leK_eq ▸ hle) h.1, h.2⟩
  call _ := none
  call_sound _ hs _ _ := by cases hs
  ret _ := none
  ret_sound _ hs _ _ := by cases hs
  push _ _ := none
  push_sound _ hs _ _ := by cases hs
  pop _ _ := none
  pop_sound _ hs _ _ := by cases hs

end VG.Proof.MlDsa.X86_64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_hint_bit_pack`

The code follows the fold form of `HintBitPack` (`Pack/Hint.lean`) step by
step: the bytes of `y` are the array of the spec, and `rax` its index, which
stays below `ω` because it counts the 1s before the current coefficient
(`hpIdx_lt`).

Constant time but for the hint: once `y` is zeroed, the two runs agree on
all the memory the function may access (the hint, which the contract lets it
leak, and `y`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of ofNat64_pred ofNat64_beq_zero wp_countdown ifp ifn b8_eq64)
open VG.Proof.MlKem (bytesAt_writeW8 bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_pack(h = rdi, hlen = rsi, omega = edx, y = rcx, len = r8)`. -/
def hintBitPackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat * 4⟩] ∧ s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 4⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 4⟩ ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩ ∧
    (dArg s .rdx, (s.gpr .r8).toNat - dArg s .rdx) ∈ hintParams ∧ dArg s .rdx ≤ (s.gpr .r8).toNat ∧
    (s.gpr .rsi).toNat = 256 * ((s.gpr .r8).toNat - dArg s .rdx) ∧
    hintOnes (hintAt s.mem (s.gpr .rdi) ((s.gpr .r8).toNat - dArg s .rdx)) ≤ dArg s .rdx
  post s s' := bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat =
    hintBitPack (dArg s .rdx) ((s.gpr .r8).toNat - dArg s .rdx)
      (hintAt s.mem (s.gpr .rdi) ((s.gpr .r8).toNat - dArg s .rdx))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    (List.range (s₁.gpr .rsi).toNat).map (fun i => (coeffAt s₁.mem (s₁.gpr .rdi) i).toNat) =
      (List.range (s₂.gpr .rsi).toNat).map (fun i => (coeffAt s₂.mem (s₂.gpr .rdi) i).toNat)

theorem ea_idx (s : State) (b i : Reg) : s.ea (atIdx b i) = s.gpr b + s.gpr i := by
  simp [State.ea, atIdx]

theorem mem_hintParams {ω k : Nat} (h : (ω, k) ∈ hintParams) : 4 ≤ k ∧ k ≤ 8 ∧ ω ≤ 80 := by
  simp only [hintParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  omega

/-- Coefficient `j` of polynomial `i` of the hint at `p`. -/
theorem hintAt_get {m : Mem} {p : Addr} {k i j : Nat} (hi : i < k) (hj : j < n) :
    ((hintAt m p k).getD i noHint)[j]! = decide (coeffAt m p (256 * i + j) ≠ 0) := by
  rw [hintAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some, getElem!_pos _ j hj, Vector.getElem_ofFn]

theorem hintAt_length (m : Mem) (p : Addr) (k : Nat) : (hintAt m p k).length = k := by simp [hintAt]

section
variable {s₀ : State} (hp : hintBitPackK.pre s₀)

/-- The arguments. -/
abbrev hω (s₀ : State) : Nat := dArg s₀ .rdx
abbrev hk (s₀ : State) : Nat := (s₀.gpr .r8).toNat - dArg s₀ .rdx
abbrev hLen (s₀ : State) : Nat := (s₀.gpr .r8).toNat
abbrev hH (s₀ : State) : List (Vector Bool n) := hintAt s₀.mem (s₀.gpr .rdi) (VG.Proof.MlDsa.X86_64.Pack.hk s₀)

include hp in
theorem hp_facts : 4 ≤ VG.Proof.MlDsa.X86_64.Pack.hk s₀ ∧ VG.Proof.MlDsa.X86_64.Pack.hk s₀ ≤ 8 ∧ VG.Proof.MlDsa.X86_64.Pack.hω s₀ ≤ 80 ∧ VG.Proof.MlDsa.X86_64.Pack.hω s₀ + VG.Proof.MlDsa.X86_64.Pack.hk s₀ = VG.Proof.MlDsa.X86_64.Pack.hLen s₀ ∧
    (s₀.gpr .rsi).toNat * 4 = 1024 * VG.Proof.MlDsa.X86_64.Pack.hk s₀ := by
  have := VG.Proof.MlDsa.X86_64.Pack.mem_hintParams hp.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.2.1
  simp only [VG.Proof.MlDsa.X86_64.Pack.hk, VG.Proof.MlDsa.X86_64.Pack.hω, VG.Proof.MlDsa.X86_64.Pack.hLen] at *
  omega

/-! ## Zeroing `y` -/

theorem hbpZeroPro_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov32 .rax (.imm 0), .mov .r9 (.reg .rcx), .mov .r10 (.reg .r8)]) s
      fun s' => (s'.gpr .rdx = BitVec.ofNat 64 (dArg s .rdx) ∧ s'.gpr .rax = 0 ∧ s'.gpr .r9 = s.gpr .rcx ∧
        s'.gpr .r10 = s.gpr .r8 ∧ s'.mem = s.mem) ∧ Keep [.rdx, .rax, .r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]
  apply BitVec.eq_of_toNat_eq; simp

theorem zeroStep_ok (s : State) (hout : InRegions s.wr (s.gpr .r9) 1) :
    WP isa (.block [.store8 (VG.Impl.MlDsa.X86_64.Pack.at_ .r9 0) .rax, .alu .add .r9 (.imm 1), .alu .sub .r10 (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r9) (BitVec.setWidth 8 (s.gpr .rax)) ∧ s'.gpr .r9 = s.gpr .r9 + 1 ∧
        s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0)) ∧ Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hout]

include hp in
theorem hbpZero_ok :
    WP isa hbpZero s₀ fun s =>
      bytesAt s.mem (s₀.gpr .rcx) (VG.Proof.MlDsa.X86_64.Pack.hLen s₀) = List.replicate (VG.Proof.MlDsa.X86_64.Pack.hLen s₀) 0 ∧
        Frame [⟨s₀.gpr .rcx, VG.Proof.MlDsa.X86_64.Pack.hLen s₀⟩] s₀.mem s.mem ∧ s.gpr .rax = 0 ∧
        s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.hω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s := by
  obtain ⟨hk4, -, -, hsum, -⟩ := VG.Proof.MlDsa.X86_64.Pack.hp_facts hp
  obtain ⟨-, hwr, -⟩ := hp
  have hl := (s₀.gpr .r8).isLt
  have e1 : VG.Proof.MlDsa.X86_64.Pack.hLen s₀ = (s₀.gpr .r8).toNat := rfl
  simp only [VG.Proof.MlDsa.X86_64.Pack.hk, VG.Proof.MlDsa.X86_64.Pack.hω, VG.Proof.MlDsa.X86_64.Pack.hLen] at hk4 hsum
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbpZeroPro_ok s₀) fun s₁ ⟨⟨dx₁, ax₁, r9₁, r10₁, m₁⟩, k₁⟩ => ?_)
  refine wp_countdown (cnt := .r10) (N := VG.Proof.MlDsa.X86_64.Pack.hLen s₀) (by omega) (by omega)
    (fun t s => s.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 t ∧ s.gpr .rax = 0 ∧
      Frame [⟨s₀.gpr .rcx, VG.Proof.MlDsa.X86_64.Pack.hLen s₀⟩] s₀.mem s.mem ∧ (∀ u < t, s.mem (s₀.gpr .rcx + BitVec.ofNat 64 u) = 0) ∧
      s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.hω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s)
    (fun t ht s ⟨h9, hax, hf, hz, hdx, hk⟩ _ => ?_) (fun s ⟨_, hax, hf, hz, hdx, hk⟩ => ⟨?_, hf, hax, hdx, hk⟩)
    ⟨by rw [r9₁]; simp, ax₁, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), dx₁,
      k₁.mono (by decide)⟩ (by rw [r10₁]; simp)
  · refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.zeroStep_ok s (by
      rw [hk.2.2, hwr, h9]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s' ⟨⟨hm, h9', h10, hz'⟩, k'⟩ => ⟨⟨?_, ?_, ?_, fun u hu => ?_, ?_, (hk.trans k').mono (by decide)⟩, h10, hz'⟩
    · rw [h9', h9, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]
    · rw [k'.gpr (by decide), hax]
    · rw [hm, h9]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [hm, h9, VG.WriteBytes.writeW8_apply]
      split
      · rw [hax]; rfl
      · rename_i hne
        refine hz u (by
          by_contra hu'
          exact hne (by rw [show u = t by omega]))
    · rw [k'.gpr (by decide), hdx]
  · exact bytesAt_eq (by simp) fun i hi => by rw [hz i hi]; simp

/-! ## The polynomials -/

/-- The spec's state after `i` polynomials. -/
abbrev hpS (s₀ : State) (i : Nat) : Array Byte × Nat :=
  (List.range i).foldl (hpPoly (VG.Proof.MlDsa.X86_64.Pack.hω s₀) (VG.Proof.MlDsa.X86_64.Pack.hH s₀)) (Array.replicate (VG.Proof.MlDsa.X86_64.Pack.hω s₀ + VG.Proof.MlDsa.X86_64.Pack.hk s₀) 0, 0)

/-- ... and `j` coefficients of polynomial `i`. -/
abbrev hpT (s₀ : State) (i j : Nat) : Array Byte × Nat :=
  (List.range j).foldl (hpStep ((VG.Proof.MlDsa.X86_64.Pack.hH s₀).getD i noHint)) (VG.Proof.MlDsa.X86_64.Pack.hpS s₀ i)

theorem hpT_zero (s₀ : State) (i : Nat) : VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i 0 = VG.Proof.MlDsa.X86_64.Pack.hpS s₀ i := by
  simp only [VG.Proof.MlDsa.X86_64.Pack.hpT, List.range_zero, List.foldl_nil]


theorem hpS_idx (s₀ : State) (i : Nat) : (VG.Proof.MlDsa.X86_64.Pack.hpS s₀ i).2 = onesBefore (VG.Proof.MlDsa.X86_64.Pack.hH s₀) i 0 := by
  rw [VG.Proof.MlDsa.X86_64.Pack.hpS, hpPolys_idx]; exact Nat.zero_add _

theorem hpT_idx (s₀ : State) (i j : Nat) : (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i j).2 = onesBefore (VG.Proof.MlDsa.X86_64.Pack.hH s₀) i j := by
  rw [VG.Proof.MlDsa.X86_64.Pack.hpT, hpSteps_idx, VG.Proof.MlDsa.X86_64.Pack.hpS_idx]; unfold onesBefore; rfl

/-- Before coefficient `j` of polynomial `i`. -/
structure CInv (s₀ : State) (i j : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (4 * (256 * i + j))
  r11 : s.gpr .r11 = BitVec.ofNat 64 j
  rax : s.gpr .rax = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i j).2
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rcx, VG.Proof.MlDsa.X86_64.Pack.hLen s₀⟩] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .rcx) (VG.Proof.MlDsa.X86_64.Pack.hLen s₀) = (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i j).1.toList

theorem hpT_succ (s₀ : State) (i j : Nat) :
    VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i (j + 1) = hpStep ((VG.Proof.MlDsa.X86_64.Pack.hH s₀).getD i noHint) (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i j) j := by
  rw [VG.Proof.MlDsa.X86_64.Pack.hpT, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem hpS_succ (s₀ : State) (i : Nat) :
    VG.Proof.MlDsa.X86_64.Pack.hpS s₀ (i + 1) = ((VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i n).1.set! (VG.Proof.MlDsa.X86_64.Pack.hω s₀ + i) (BitVec.ofNat 8 (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i n).2), (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i n).2) := by
  rw [VG.Proof.MlDsa.X86_64.Pack.hpS, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem hbpLoad_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4) :
    WP isa (.block [.mov32 .rsi (.mem (VG.Impl.MlDsa.X86_64.Pack.at_ .rdi 0)), .alu32 .cmp .rsi (.imm 0)]) s fun s' =>
      (s'.zf = some (s.mem.readW (s.gpr .rdi) 32 - 0 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rsi] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hin]

theorem hbpSet_ok (s : State) (hout : InRegions s.wr (s.gpr .rcx + s.gpr .rax) 1) :
    WP isa (.block [.store8 (atIdx .rcx .rax) .r11, .alu .add .rax (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rcx + s.gpr .rax) (BitVec.setWidth 8 (s.gpr .r11)) ∧
        s'.gpr .rax = s.gpr .rax + 1) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [VG.Proof.MlDsa.X86_64.Pack.ea_idx, hout]

theorem hbpNext_ok (s : State) :
    WP isa (.block [.alu .add .rdi (.imm 4), .alu .add .r11 (.imm 1), .alu32 .cmp .r11 (.imm 256)]) s fun s' =>
      (s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .r11 = s.gpr .r11 + 1 ∧
        s'.zf = some (BitVec.setWidth 32 (s.gpr .r11 + 1) - 256 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rdi, .r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem ofNat_succ64 (x : Nat) : BitVec.ofNat 64 x + 1 = BitVec.ofNat 64 (x + 1) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

theorem cmp256 {j : Nat} (hj : j < 256) : (BitVec.setWidth 32 (BitVec.ofNat 64 (j + 1)) - 256 == 0) = decide (j + 1 = 256) := by
  rw [VG.Proof.MlKem.X86_64.sub_beq_zero32]
  simp only [decide_eq_decide]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  · intro h; rw [h]; rfl

include hp in
theorem coef_ok {i j : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.hk s₀) (hj : j < 256) {s : State} (hI : VG.Proof.MlDsa.X86_64.Pack.CInv s₀ i j s) :
    WP isa hbpCoef s fun s' => VG.Proof.MlDsa.X86_64.Pack.CInv s₀ i (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 256)) ∧
      Keep [.rax, .rsi, .rdi, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := VG.Proof.MlDsa.X86_64.Pack.hp_facts hp
  obtain ⟨hrd, hwr, hsep, -, -, -, -, -, hones⟩ := hp
  have e1 : VG.Proof.MlDsa.X86_64.Pack.hLen s₀ = (s₀.gpr .r8).toNat := rfl
  have e2 : VG.Proof.MlDsa.X86_64.Pack.hk s₀ = (s₀.gpr .r8).toNat - dArg s₀ .rdx := rfl
  have e3 : VG.Proof.MlDsa.X86_64.Pack.hω s₀ = dArg s₀ .rdx := rfl
  have hpos : 256 * i + j < 256 * VG.Proof.MlDsa.X86_64.Pack.hk s₀ := by omega
  -- The word, on entry.
  have hR : (⟨s₀.gpr .rdi, (s₀.gpr .rsi).toNat * 4⟩ : Region).Contains (coeffAddr (s₀.gpr .rdi) (256 * i + j)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  have hw : s.mem.readW (s.gpr .rdi) 32 = coeffAt s₀.mem (s₀.gpr .rdi) (256 * i + j) := by
    rw [hI.rdi]
    exact hI.frame.readW hR (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by decide)
  unfold hbpCoef
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbpLoad_ok s (by rw [hI.rd, hI.wr, hrd, hI.rdi]; exact ⟨_, by simp, hR⟩))
    fun s₁ ⟨⟨z₁, m₁⟩, k₁⟩ => ?_)
  have hbit := VG.Proof.MlDsa.X86_64.Pack.hintAt_get (m := s₀.mem) (p := s₀.gpr .rdi) hi hj
  have hT := VG.Proof.MlDsa.X86_64.Pack.hpT_succ s₀ i j
  have hidx := VG.Proof.MlDsa.X86_64.Pack.hpT_idx s₀ i j
  refine WP.seq ?_
  -- The branch.
  have hc : isa.eval .ne s₁ = some (decide (coeffAt s₀.mem (s₀.gpr .rdi) (256 * i + j) ≠ 0)) := by
    show Option.map _ s₁.zf = _
    rw [z₁, hw, VG.Proof.MlKem.X86_64.sub_beq_zero32]; simp
  refine WP.ite (M := isa) _ hc (fun h1 => ?_) (fun h0 => ?_)
  · -- A 1: `y[index] ← j`.
    have hlt : (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i j).2 < VG.Proof.MlDsa.X86_64.Pack.hLen s₀ := by
      have : onesBefore (VG.Proof.MlDsa.X86_64.Pack.hH s₀) i j < hintOnes (VG.Proof.MlDsa.X86_64.Pack.hH s₀) :=
        hpIdx_lt (VG.Proof.MlDsa.X86_64.Pack.hintAt_length s₀.mem (s₀.gpr .rdi) _) hi hj (by rw [hbit]; exact h1)
      have hones' : hintOnes (VG.Proof.MlDsa.X86_64.Pack.hH s₀) ≤ VG.Proof.MlDsa.X86_64.Pack.hω s₀ := hones
      rw [hidx]; omega
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbpSet_ok s₁ (by
      rw [k₁.2.2, hI.wr, hwr, k₁.gpr (by decide), k₁.gpr (by decide), hI.rcx, hI.rax]
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)) fun s₂ ⟨⟨m₂, ax₂⟩, k₂⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbpNext_ok s₂) fun s₃ ⟨⟨di₃, r11₃, z₃, m₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [di₃, k₂.gpr (by decide), k₁.gpr (by decide), hI.rdi, BitVec.add_assoc,
        show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [r11₃, k₂.gpr (by decide), k₁.gpr (by decide), hI.r11, VG.Proof.MlDsa.X86_64.Pack.ofNat_succ64]
    · rw [k₃.gpr (by decide), ax₂, k₁.gpr (by decide), hI.rax, hT, hpStep, hbit]
      simp only [h1, ↓reduceIte, VG.Proof.MlDsa.X86_64.Pack.ofNat_succ64]
    · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hI.rcx]
    · rw [k₃.2.1, k₂.2.1, k₁.2.1, hI.rd]
    · rw [k₃.2.2, k₂.2.2, k₁.2.2, hI.wr]
    · rw [m₃, m₂, m₁, k₁.gpr (by decide), k₁.gpr (by decide), hI.rcx, hI.rax]
      exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [m₃, m₂, m₁, k₁.gpr (by decide), k₁.gpr (by decide), hI.rcx, hI.rax, bytesAt_writeW8 _ _ hlt (by omega),
        hI.y, hT, hpStep, hbit, k₁.gpr (by decide), hI.r11, b8_eq64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [h1, ↓reduceIte, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide), hI.r11, VG.Proof.MlDsa.X86_64.Pack.ofNat_succ64, VG.Proof.MlDsa.X86_64.Pack.cmp256 hj]
    · exact ((k₁.trans k₂).trans k₃).mono (by decide)
  · -- A 0.
    refine WP.block_nil (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbpNext_ok s₁) fun s₃ ⟨⟨di₃, r11₃, z₃, m₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩)
    · rw [di₃, k₁.gpr (by decide), hI.rdi, BitVec.add_assoc,
        show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show 4 * (256 * i + j) + 4 = 4 * (256 * i + (j + 1)) by omega]
    · rw [r11₃, k₁.gpr (by decide), hI.r11, VG.Proof.MlDsa.X86_64.Pack.ofNat_succ64]
    · rw [k₃.gpr (by decide), k₁.gpr (by decide), hI.rax, hT, hpStep, hbit]
      simp only [h0, Bool.false_eq_true, ↓reduceIte]
    · rw [k₃.gpr (by decide), k₁.gpr (by decide), hI.rcx]
    · rw [k₃.2.1, k₁.2.1, hI.rd]
    · rw [k₃.2.2, k₁.2.2, hI.wr]
    · rw [m₃, m₁]; exact hI.frame
    · rw [m₃, m₁, hI.y, hT, hpStep, hbit]
      simp only [h0, Bool.false_eq_true, ↓reduceIte]
    · rw [z₃, k₁.gpr (by decide), hI.r11, VG.Proof.MlDsa.X86_64.Pack.ofNat_succ64, VG.Proof.MlDsa.X86_64.Pack.cmp256 hj]
    · exact (k₁.trans k₃).mono (by decide)

include hp in
theorem inner_ok {i : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.hk s₀) {s : State} (hI : VG.Proof.MlDsa.X86_64.Pack.CInv s₀ i 0 s) :
    WP isa (.loop hbpCoef .ne) s fun s' => VG.Proof.MlDsa.X86_64.Pack.CInv s₀ i 256 s' ∧ Keep [.rax, .rsi, .rdi, .r11] s s' := by
  refine WP.loop (M := isa) (fun m s' => ∃ j, j < 256 ∧ m = 256 - j ∧ VG.Proof.MlDsa.X86_64.Pack.CInv s₀ i j s' ∧
    Keep [.rax, .rsi, .rdi, .r11] s s') (fun m s' ⟨j, hj, hm, hI', hk'⟩ => ?_) 256 s
    ⟨0, by decide, rfl, hI, Keep.refl _ _⟩
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.coef_ok hp hi hj hI') fun s'' ⟨hI'', hz, hk''⟩ => ?_
  have hc : isa.eval .ne s'' = some (!decide (j + 1 = 256)) := by
    show Option.map _ s''.zf = _; rw [hz]; rfl
  by_cases e : j + 1 = 256
  · refine .inl ⟨by rw [hc, e]; rfl, ?_, (hk'.trans hk'').mono (by decide)⟩
    rw [← e]; exact hI''
  · refine .inr ⟨by rw [hc, decide_eq_false e]; rfl, 256 - (j + 1), by omega, j + 1, by omega, rfl, hI'',
      (hk'.trans hk'').mono (by decide)⟩

/-- Before polynomial `i`. -/
structure HPInv (s₀ : State) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (4 * (256 * i))
  rax : s.gpr .rax = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.hpS s₀ i).2
  rcx : s.gpr .rcx = s₀.gpr .rcx
  r9 : s.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.hω s₀ + i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rcx, VG.Proof.MlDsa.X86_64.Pack.hLen s₀⟩] s₀.mem s.mem
  y : bytesAt s.mem (s₀.gpr .rcx) (VG.Proof.MlDsa.X86_64.Pack.hLen s₀) = (VG.Proof.MlDsa.X86_64.Pack.hpS s₀ i).1.toList

theorem zeroR11_ok (s : State) :
    WP isa (.block [.mov32 .r11 (.imm 0)]) s fun s' => (s'.gpr .r11 = 0 ∧ s'.mem = s.mem) ∧ Keep [.r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

include hp in
theorem poly_ok {i : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.hk s₀) {s : State} (hP : VG.Proof.MlDsa.X86_64.Pack.HPInv s₀ i s) :
    WP isa hbpPoly s fun s' => VG.Proof.MlDsa.X86_64.Pack.HPInv s₀ (i + 1) s' ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
      s'.zf = some (s.gpr .r10 - 1 == 0) ∧ Keep [.rax, .rsi, .rdi, .r9, .r10, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := VG.Proof.MlDsa.X86_64.Pack.hp_facts hp
  have hwr := hp.2.1
  have e1 : VG.Proof.MlDsa.X86_64.Pack.hLen s₀ = (s₀.gpr .r8).toNat := rfl
  unfold hbpPoly
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.zeroR11_ok s) fun s₁ ⟨⟨r11₁, m₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.inner_ok hp hi (s := s₁) ⟨by rw [k₁.gpr (by decide), hP.rdi]; rfl, by rw [r11₁]; rfl,
    by rw [k₁.gpr (by decide), hP.rax, VG.Proof.MlDsa.X86_64.Pack.hpT_zero], by rw [k₁.gpr (by decide), hP.rcx], by rw [k₁.2.1, hP.rd],
    by rw [k₁.2.2, hP.wr], by rw [m₁]; exact hP.frame, by rw [m₁, hP.y, VG.Proof.MlDsa.X86_64.Pack.hpT_zero]⟩) fun s₂ ⟨hI, k₂⟩ => ?_)
  have r9₂ : s₂.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.hω s₀ + i) := by
    rw [k₂.gpr (by decide), k₁.gpr (by decide), hP.r9]
  have hidx : (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i 256).2 < 2 ^ 8 := by
    have := VG.Proof.MlDsa.X86_64.Pack.hpT_idx s₀ i 256
    have h1 : onesBefore (VG.Proof.MlDsa.X86_64.Pack.hH s₀) i 256 ≤ hintOnes (VG.Proof.MlDsa.X86_64.Pack.hH s₀) := onesBefore_n_le (VG.Proof.MlDsa.X86_64.Pack.hintAt_length _ _ _) hi
    have hones' : hintOnes (VG.Proof.MlDsa.X86_64.Pack.hH s₀) ≤ VG.Proof.MlDsa.X86_64.Pack.hω s₀ := hp.2.2.2.2.2.2.2.2
    rw [this]; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.zeroStep_ok s₂ (by
      rw [hI.wr, hwr, r9₂]
      exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩))
    fun s₃ ⟨⟨m₃, r9₃, r10₃, z₃⟩, k₃⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [k₃.gpr (by decide), hI.rdi, show 4 * (256 * i + 256) = 4 * (256 * (i + 1)) by omega]
  · rw [k₃.gpr (by decide), hI.rax, VG.Proof.MlDsa.X86_64.Pack.hpS_succ]
  · rw [k₃.gpr (by decide), hI.rcx]
  · rw [r9₃, r9₂, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat,
      Nat.add_assoc]
  · rw [k₃.2.1, hI.rd]
  · rw [k₃.2.2, hI.wr]
  · rw [m₃, r9₂]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  · rw [m₃, r9₂, bytesAt_writeW8 _ _ (by omega) (by omega), hI.y, hI.rax, VG.Proof.MlDsa.X86_64.Pack.hpS_succ, b8_eq64, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show (VG.Proof.MlDsa.X86_64.Pack.hpT s₀ i 256).2 < 2 ^ 64 by omega), Array.set!_eq_setIfInBounds,
      Array.toList_setIfInBounds]
  · rw [r10₃, k₂.gpr (by decide), k₁.gpr (by decide)]
  · rw [z₃, k₂.gpr (by decide), k₁.gpr (by decide)]
  · exact ((k₁.trans k₂).trans k₃).mono (by decide)

theorem hbpSetup_ok (s : State) :
    WP isa (.block [.mov .r9 (.reg .rcx), .alu .add .r9 (.reg .rdx), .mov .r10 (.reg .r8), .alu .sub .r10 (.reg .rdx)])
      s fun s' => (s'.gpr .r9 = s.gpr .rcx + s.gpr .rdx ∧ s'.gpr .r10 = s.gpr .r8 - s.gpr .rdx ∧ s'.mem = s.mem) ∧
        Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

include hp in
theorem hbp_wp :
    WP isa Impl.MlDsa.X86_64.Pack.hintBitPack s₀ fun s' =>
      hintBitPackK.post s₀ s' ∧ Frame [⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat⟩] s₀.mem s'.mem := by
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := VG.Proof.MlDsa.X86_64.Pack.hp_facts hp
  have e1 : VG.Proof.MlDsa.X86_64.Pack.hLen s₀ = (s₀.gpr .r8).toNat := rfl
  have e2 : VG.Proof.MlDsa.X86_64.Pack.hk s₀ = (s₀.gpr .r8).toNat - dArg s₀ .rdx := rfl
  have e3 : VG.Proof.MlDsa.X86_64.Pack.hω s₀ = dArg s₀ .rdx := rfl
  unfold Impl.MlDsa.X86_64.Pack.hintBitPack
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbpZero_ok hp) fun s₁ ⟨hy₁, hf₁, ax₁, dx₁, k₁⟩ => ?_)
  unfold hbpMain
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbpSetup_ok s₁) fun s₂ ⟨⟨r9₂, r10₂, m₂⟩, k₂⟩ => ?_)
  refine wp_countdown (cnt := .r10) (N := VG.Proof.MlDsa.X86_64.Pack.hk s₀) (by omega) (by omega) (fun i s => VG.Proof.MlDsa.X86_64.Pack.HPInv s₀ i s)
    (fun i hi s hP _ => WP.mono (VG.Proof.MlDsa.X86_64.Pack.poly_ok hp hi hP) fun s' ⟨h, h10, hz, _⟩ => ⟨h, h10, hz⟩)
    (fun s hP => ⟨hP.y.trans (hintBitPack_eq _ _ _).symm, hP.frame⟩) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · rw [k₂.gpr (by decide), k₁.gpr (by decide)]; simp
  · rw [k₂.gpr (by decide), ax₁]; rfl
  · rw [k₂.gpr (by decide), k₁.gpr (by decide)]
  · rw [r9₂, k₁.gpr (by decide), dx₁]; rfl
  · rw [k₂.2.1, k₁.2.1]
  · rw [k₂.2.2, k₁.2.2]
  · rw [m₂]; exact hf₁
  · rw [m₂, hy₁]; show _ = (Array.replicate (VG.Proof.MlDsa.X86_64.Pack.hω s₀ + VG.Proof.MlDsa.X86_64.Pack.hk s₀) (0 : Byte)).toList
    rw [Array.toList_replicate, hsum]
  · rw [r10₂, k₁.gpr (by decide), dx₁]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := (s₀.gpr .r8).isLt
    omega

end

theorem hintBitPack_correct (s : State) (hs : hintBitPackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.hintBitPack s t s' ∧ abiPreserved s s' ∧ hintBitPackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.hintBitPack)
    [.rax, .rdx, .rsi, .rdi, .r9, .r10, .r11] (VG.Proof.MlDsa.X86_64.Pack.hbp_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

/-! ## Constant time -/

/-- The bytes of words that agree. -/
theorem bytes_of_words {m₁ m₂ : Mem} {p : Addr} {N : Nat}
    (h : (List.range N).map (fun i => (coeffAt m₁ p i).toNat) = (List.range N).map (fun i => (coeffAt m₂ p i).toNat))
    {a : Addr} (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m₁ a = m₂ a := by
  simp only [Region.Contains] at ha
  have hw : ∀ i < N, coeffAt m₁ p i = coeffAt m₂ p i := fun i hi =>
    BitVec.eq_of_toNat_eq (List.map_inj_left.mp h i (List.mem_range.mpr hi))
  have hi : (a - p).toNat / 4 < N := by omega
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m₁ (coeffAddr p _) ht, Mem.readW_byte m₂ (coeffAddr p _) ht, ← coeffAt_eq, ← coeffAt_eq,
    hw _ hi]

/-- The taint of the loops: the pointers, the lengths, `ω` and the index. -/
abbrev hbpTaint : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rcx, .rdx, .r8, .rax]

theorem hintBitPack_ct :
    ConstantTime isa hintBitPackK.pre hintBitPackK.pub Impl.MlDsa.X86_64.Pack.hintBitPack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Pack.MAgree VG.Proof.MlDsa.X86_64.Pack.hbpTaint) ?_ (RelCT.taint (A := VG.Proof.MlDsa.X86_64.Pack.memTaint) VG.Proof.MlDsa.X86_64.Pack.hbpTaint (fun _ _ h => h) (by taint_decide))
  refine Proof.MlKem.X86_64.RelCT.postDep
    (RelCT.taint (A := taint) (regsLo [.rdi, .rsi, .rcx, .r8, .rsp] [.rdx])
      (fun _ _ ⟨_, _, hp⟩ => agree_regsLo (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1])
        fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2.2.1)
      (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlDsa.X86_64.Pack.hbpZero_ok hx, VG.Proof.MlDsa.X86_64.Pack.hbpZero_ok hy⟩) fun x y x' y' ⟨hx, hy, hp⟩ fx fy => ?_
  obtain ⟨hy₁, hf₁, ax₁, dx₁, k₁⟩ := fx
  obtain ⟨hy₂, hf₂, ax₂, dx₂, k₂⟩ := fy
  obtain ⟨di, si, ci, r8, -, dx, hleak⟩ := hp
  have hdx : dArg x .rdx = dArg y .rdx := by unfold dArg; rw [dx]
  have hrd : x'.rd = y'.rd := by rw [k₁.2.1, k₂.2.1, hx.1, hy.1, di, si]
  have hwr : x'.wr = y'.wr := by rw [k₁.2.2, k₂.2.2, hx.2.1, hy.2.1, ci, r8]
  obtain ⟨hk4, hk8, hω80, hsum, hrsi⟩ := VG.Proof.MlDsa.X86_64.Pack.hp_facts hx
  refine ⟨X86_64.Taint.agree_ofRegs fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), di]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), ci]
    · rw [dx₁, dx₂]; exact congrArg _ hdx
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), r8]
    · rw [ax₁, ax₂]
  · rw [k₁.2.1, k₁.2.2, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- The hint: as on entry, where the runs agree.
      have hdis : ∀ r ∈ [(⟨x.gpr .rcx, (x.gpr .r8).toNat⟩ : Region)], ¬ r.Contains a 1 := by
        intro r hr hc'; simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'
      rw [hf₁ a hdis, hf₂ a (fun r hr hc' => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [VG.Proof.MlDsa.X86_64.Pack.hLen, ← ci, ← r8] at hc'
        exact hx.2.2.1 a hc hc')]
      exact VG.Proof.MlDsa.X86_64.Pack.bytes_of_words (by rw [← di, ← si] at hleak; exact hleak) hc
    · -- `y`: zeros.
      have hlt : (a - x.gpr .rcx).toNat < (x.gpr .r8).toNat := by simp only [Region.Contains] at hc; omega
      have eL : VG.Proof.MlDsa.X86_64.Pack.hLen x = (x.gpr .r8).toNat := rfl
      have eLy : VG.Proof.MlDsa.X86_64.Pack.hLen y = (x.gpr .r8).toNat := by show (y.gpr .r8).toNat = _; rw [r8]
      have ea : a = x.gpr .rcx + BitVec.ofNat 64 (a - x.gpr .rcx).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have h₁ := congrArg (·.getD (a - x.gpr .rcx).toNat 0) hy₁
      have h₂ := congrArg (·.getD (a - x.gpr .rcx).toNat 0) hy₂
      rw [eL, bytesAt_getD _ _ hlt, ← ea] at h₁
      rw [eLy, ← ci, bytesAt_getD _ _ hlt, ← ea] at h₂
      rw [h₁, h₂]

/-- A state satisfying the precondition. -/
def hintBitPackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1024 | .rdx => 80 | .rcx => 0x3000 | .r8 => 84 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 4096⟩]
  wr := [⟨0x3000, 84⟩]

theorem coeffAt_zero' (p : Addr) (i : Nat) : coeffAt (fun _ => 0#8) p i = 0#32 := VG.Proof.MlDsa.X86_64.Pack.coeffAt_zero p i

theorem filter_false : ((Vector.ofFn fun _ : Fin n => false).toList.filter id) = [] := by
  rw [List.filter_eq_nil_iff]; intro a ha; simp at ha; simp [ha]

theorem sum_zero : ∀ l : List Nat, (l.map fun _ => 0).sum = 0
  | [] => rfl
  | _ :: l => by rw [List.map_cons, List.sum_cons, VG.Proof.MlDsa.X86_64.Pack.sum_zero l]

theorem hintOnes_zero (p : Addr) (k : Nat) : hintOnes (hintAt (fun _ => 0) p k) = 0 := by
  simp [hintOnes, hintAt, VG.Proof.MlDsa.X86_64.Pack.coeffAt_zero', Function.comp_def, VG.Proof.MlDsa.X86_64.Pack.filter_false, VG.Proof.MlDsa.X86_64.Pack.sum_zero]

theorem hintBitPack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.hintBitPack (hintBitPackContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Pack.hintBitPack_correct VG.Proof.MlDsa.X86_64.Pack.hintBitPack_ct
    { pre := by sig_implies_pre [hintBitPackContract, hintBitPackSig, VG.Proof.MlDsa.X86_64.Pack.hintBitPackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [hintBitPackContract, hintBitPackSig, VG.Proof.MlDsa.X86_64.Pack.hintBitPackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [hintBitPackContract, hintBitPackSig, VG.Proof.MlDsa.X86_64.Pack.hintBitPackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.X86_64.Pack.hintBitPackSat, ?_⟩
        sig_pre [hintBitPackContract, hintBitPackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | (rw [VG.Proof.MlDsa.X86_64.Pack.hintOnes_zero]; exact Nat.zero_le _)
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_hint_bit_unpack`

The code follows the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Pack/Hint.lean`) step by step: while no check has failed, the words of `h`
are the hint of the spec (`HArr`) and `rax` its index; once one has, `rax` is
256, which skips the rest (`SRel`).

Constant time but for its input: once `h` is zeroed, the two runs agree on
all the memory the function may access (the input `y`, which the contract
lets it leak, and `h`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.X86_64.Pack

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.X86_64 (Keep Keep.refl Keep.trans Keep.mono Keep.gpr WP.keep retR pR dArg regsLo agree_regsLo
  gprPreserved_of wp_countdown ifp ifn b8_eq64 toNat_setWidth64_8)
open VG.Proof.MlKem (bytesAt_length bytesAt_getD bytesAt_eq)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_unpack(y = rdi, len = rsi, omega = edx, h = rcx, hlen = r8)`. -/
def hintBitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩] ∧ s.wr = [⟨s.gpr .rcx, (s.gpr .r8).toNat * 4⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ⟨s.gpr .rcx, (s.gpr .r8).toNat * 4⟩ ∧
    (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ ∧ (VG.Proof.MlKem.X86_64.retR s).Disjoint ⟨s.gpr .rcx, (s.gpr .r8).toNat * 4⟩ ∧
    (dArg s .rdx, (s.gpr .rsi).toNat - dArg s .rdx) ∈ hintParams ∧ dArg s .rdx ≤ (s.gpr .rsi).toNat ∧
    (s.gpr .r8).toNat = 256 * ((s.gpr .rsi).toNat - dArg s .rdx)
  post s s' :=
    match hintBitUnpack (dArg s .rdx) ((s.gpr .rsi).toNat - dArg s .rdx)
      (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) with
    | some hint => (s'.gpr .rax).setWidth 32 = 1 ∧ HintIs s'.mem (s.gpr .rcx) ((s.gpr .rsi).toNat - dArg s .rdx) hint
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32 ∧
    leakBytes (bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat) =
      leakBytes (bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat)

section
variable {s₀ : State} (hp : hintBitUnpackK.pre s₀)

/-- The arguments. -/
abbrev uω (s₀ : State) : Nat := dArg s₀ .rdx
abbrev uk (s₀ : State) : Nat := (s₀.gpr .rsi).toNat - dArg s₀ .rdx
abbrev uLen (s₀ : State) : Nat := (s₀.gpr .rsi).toNat
abbrev uY (s₀ : State) : Array Byte := (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat).toArray
/-- The region of `h`. -/
abbrev uR (s₀ : State) : Region := ⟨s₀.gpr .rcx, (s₀.gpr .r8).toNat * 4⟩

include hp in
theorem up_facts : 4 ≤ VG.Proof.MlDsa.X86_64.Pack.uk s₀ ∧ VG.Proof.MlDsa.X86_64.Pack.uk s₀ ≤ 8 ∧ VG.Proof.MlDsa.X86_64.Pack.uω s₀ ≤ 80 ∧ VG.Proof.MlDsa.X86_64.Pack.uω s₀ + VG.Proof.MlDsa.X86_64.Pack.uk s₀ = VG.Proof.MlDsa.X86_64.Pack.uLen s₀ ∧
    (s₀.gpr .r8).toNat = 256 * VG.Proof.MlDsa.X86_64.Pack.uk s₀ := by
  have := VG.Proof.MlDsa.X86_64.Pack.mem_hintParams hp.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.1
  have := hp.2.2.2.2.2.2.2
  simp only [VG.Proof.MlDsa.X86_64.Pack.uk, VG.Proof.MlDsa.X86_64.Pack.uω, VG.Proof.MlDsa.X86_64.Pack.uLen] at *
  omega

/-! ## Zeroing `h` -/

theorem hbuZeroPro_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.reg .rdx), .mov32 .rax (.imm 0), .mov .r9 (.reg .rcx), .mov .r10 (.reg .r8)]) s
      fun s' => (s'.gpr .rdx = BitVec.ofNat 64 (dArg s .rdx) ∧ s'.gpr .rax = 0 ∧ s'.gpr .r9 = s.gpr .rcx ∧
        s'.gpr .r10 = s.gpr .r8 ∧ s'.mem = s.mem) ∧ Keep [.rdx, .rax, .r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [dArg]
  apply BitVec.eq_of_toNat_eq; simp

theorem zeroStep32_ok (s : State) (hout : InRegions s.wr (s.gpr .r9) 4) :
    WP isa (.block [.store32 (VG.Impl.MlDsa.X86_64.Pack.at_ .r9 0) .rax, .alu .add .r9 (.imm 4), .alu .sub .r10 (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .r9) (BitVec.setWidth 32 (s.gpr .rax)) ∧ s'.gpr .r9 = s.gpr .r9 + 4 ∧
        s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0)) ∧ Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hout]

include hp in
theorem hbuZero_ok :
    WP isa hbuZero s₀ fun s =>
      (∀ t < (s₀.gpr .r8).toNat, coeffAt s.mem (s₀.gpr .rcx) t = 0) ∧ Frame [VG.Proof.MlDsa.X86_64.Pack.uR s₀] s₀.mem s.mem ∧
        s.gpr .rax = 0 ∧ s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.uω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s := by
  obtain ⟨hk4, hk8, -, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  obtain ⟨-, hwr, -⟩ := hp
  have hl := (s₀.gpr .r8).isLt
  simp only [VG.Proof.MlDsa.X86_64.Pack.uk, VG.Proof.MlDsa.X86_64.Pack.uω, VG.Proof.MlDsa.X86_64.Pack.uLen] at hk4 hk8 hsum hr8
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuZeroPro_ok s₀) fun s₁ ⟨⟨dx₁, ax₁, r9₁, r10₁, m₁⟩, k₁⟩ => ?_)
  refine wp_countdown (cnt := .r10) (N := (s₀.gpr .r8).toNat) (by omega) (by omega)
    (fun t s => s.gpr .r9 = s₀.gpr .rcx + BitVec.ofNat 64 (4 * t) ∧ s.gpr .rax = 0 ∧
      Frame [VG.Proof.MlDsa.X86_64.Pack.uR s₀] s₀.mem s.mem ∧ (∀ u < t, coeffAt s.mem (s₀.gpr .rcx) u = 0) ∧
      s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.uω s₀) ∧ Keep [.rdx, .rax, .r9, .r10] s₀ s)
    (fun t ht s ⟨h9, hax, hf, hz, hdx, hk⟩ _ => ?_) (fun s ⟨_, hax, hf, hz, hdx, hk⟩ => ⟨hz, hf, hax, hdx, hk⟩)
    ⟨by rw [r9₁]; simp, ax₁, by rw [m₁]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _), dx₁,
      k₁.mono (by decide)⟩ (by rw [r10₁]; simp)
  · refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.zeroStep32_ok s (by
      rw [hk.2.2, hwr, h9]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩))
      fun s' ⟨⟨hm, h9', h10, hz'⟩, k'⟩ => ⟨⟨?_, ?_, ?_, fun u hu => ?_, ?_, (hk.trans k').mono (by decide)⟩, h10, hz'⟩
    · rw [h9', h9, BitVec.add_assoc, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat,
        show 4 * t + 4 = 4 * (t + 1) by omega]
    · rw [k'.gpr (by decide), hax]
    · rw [hm, h9]
      exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
    · rw [hm, h9]
      by_cases e : u = t
      · subst e; rw [coeffAt_eq, Mem.readW_writeW_self32, hax]; rfl
      · rw [coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide),
          ← coeffAt_eq, hz u (by omega)]
    · rw [k'.gpr (by decide), hdx]

/-! ## The hint in memory -/

/-- The words of `h` are the hint `hA` of the spec. -/
def HArr (s₀ : State) (m : Mem) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = VG.Proof.MlDsa.X86_64.Pack.uk s₀ ∧ ∀ i < VG.Proof.MlDsa.X86_64.Pack.uk s₀, ∀ j < 256,
    coeffAt m (s₀.gpr .rcx) (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `rax`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .rax = BitVec.ofNat 64 idx ∧ idx ≤ VG.Proof.MlDsa.X86_64.Pack.uω s₀ ∧ VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s.mem hA
  | none, s => s.gpr .rax = 256

/-- What stays the same from the loops on. -/
structure UCom (s₀ : State) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi
  rdx : s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.uω s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.MlDsa.X86_64.Pack.uR s₀] s₀.mem s.mem

theorem UCom.of_keep {s₀ s s' : State} (h : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s) {rs : List Reg} (hk : Keep rs s s')
    (hrdi : Reg.rdi ∉ rs) (hrdx : Reg.rdx ∉ rs) (hm : Frame [VG.Proof.MlDsa.X86_64.Pack.uR s₀] s.mem s'.mem) : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s' :=
  ⟨(hk.gpr hrdi).trans h.rdi, (hk.gpr hrdx).trans h.rdx, hk.2.1.trans h.rd, hk.2.2.trans h.wr, h.frame.trans hm⟩

/-- Coefficient `256i + b`, the one `hbuSet` writes. -/
theorem setAddr (p : Addr) (i b : Nat) :
    p + BitVec.ofNat 64 (1024 * i) + BitVec.ofNat 64 b * 4 = coeffAddr p (256 * i + b) := by
  rw [show BitVec.ofNat 64 b * 4 = BitVec.ofNat 64 (4 * b) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (4 : BitVec 64).toNat = 4 from rfl]
      omega,
    BitVec.add_assoc, BitVec.ofNat_add_ofNat, coeffAddr]
  congr 2; omega

include hp in
theorem harr_set {m : Mem} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.X86_64.Pack.HArr s₀ m hA) {i b : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.uk s₀)
    (hb : b < 256) :
    VG.Proof.MlDsa.X86_64.Pack.HArr s₀ (m.writeW (coeffAddr (s₀.gpr .rcx) (256 * i + b)) (1 : BitVec 32)) (huSet i b hA) := by
  obtain ⟨hk4, hk8, -, -, -⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

include hp in
theorem harr_zero {m : Mem} (hz : ∀ t < (s₀.gpr .r8).toNat, coeffAt m (s₀.gpr .rcx) t = 0) :
    VG.Proof.MlDsa.X86_64.Pack.HArr s₀ m (Array.replicate (VG.Proof.MlDsa.X86_64.Pack.uk s₀) noHint) := by
  obtain ⟨-, -, -, -, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

include hp in
/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s : State} (hc : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s) {t : Nat} (ht : t < VG.Proof.MlDsa.X86_64.Pack.uLen s₀) :
    s.mem (s₀.gpr .rdi + BitVec.ofNat 64 t) = (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD t 0 := by
  have e : VG.Proof.MlDsa.X86_64.Pack.uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.2.2.1 _ (Offset.contains_base _ (by omega) (by omega)) hc'

theorem hbuSet_ok (s : State) (hout : InRegions s.wr (s.gpr .rcx + s.gpr .rsi * 4) 4) :
    WP isa (.block hbuSet) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rcx + s.gpr .rsi * 4) (1 : BitVec 32) ∧ s'.gpr .rax = s.gpr .rax + 1) ∧
        Keep [.r8, .rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold hbuSet
  xrun [hout, show ∀ (t : State) (b i : Reg), t.ea (atIdx b i 4) = t.gpr b + t.gpr i * 4 from fun t b i => by
    simp [State.ea, atIdx]]

theorem ea_idx4 (t : State) (b i : Reg) : t.ea (atIdx b i 4) = t.gpr b + t.gpr i * 4 := by
  simp [State.ea, atIdx]

theorem ea_idxm1 (t : State) (b i : Reg) : t.ea (atIdx b i 1 (-1)) = t.gpr b + t.gpr i + BitVec.ofInt 64 (-1) := by
  simp [State.ea, atIdx]

theorem ofNat_pred64 (p : Addr) {x : Nat} (h : 1 ≤ x) (hx : x < 2 ^ 64) :
    p + BitVec.ofNat 64 x + BitVec.ofInt 64 (-1) = p + BitVec.ofNat 64 (x - 1) := by
  bv_omega

theorem cmpReg_ok (a b : Reg) (s : State) :
    WP isa (.block [.alu .cmp a (.reg b)]) s fun s' =>
      (s'.cf = some (decide ((s.gpr a).toNat < (s.gpr b).toNat)) ∧ s'.mem = s.mem) ∧ Keep [] s s' := by
  refine WP.mono (Q := fun (s' : State) => s'.cf = some (decide ((s.gpr a).toNat < (s.gpr b).toNat)) ∧ s'.mem = s.mem ∧
    s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr) (by xrun) fun s' ⟨h1, h2, h3, h4, h5⟩ =>
    ⟨⟨h1, h2⟩, fun r _ => congrFun h3 r, h4, h5⟩

/-- Where the loops of polynomial `i` are. -/
structure PCom (s₀ : State) (i bound : Nat) (s : State) : Prop where
  com : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s
  rcx : s.gpr .rcx = s₀.gpr .rcx + BitVec.ofNat 64 (1024 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 bound

theorem PCom.of_keep {s₀ s s' : State} {i bound : Nat} (h : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s) {rs : List Reg} (hk : Keep rs s s')
    (hrs : ∀ r ∈ rs, r ≠ .rdi ∧ r ≠ .rdx ∧ r ≠ .rcx ∧ r ≠ .r11) (hm : Frame [VG.Proof.MlDsa.X86_64.Pack.uR s₀] s.mem s'.mem) :
    VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s' :=
  ⟨h.com.of_keep hk (fun h' => (hrs _ h').1 rfl) (fun h' => (hrs _ h').2.1 rfl) hm,
    (hk.gpr fun h' => (hrs _ h').2.2.1 rfl).trans h.rcx, (hk.gpr fun h' => (hrs _ h').2.2.2 rfl).trans h.r11⟩

include hp in
/-- Setting coefficient `y[index]` of polynomial `i`. -/
theorem set_ok {i bound idx : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.uk s₀) {hA : Array (Vector Bool n)}
    {s : State} (hP : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s) (hax : s.gpr .rax = BitVec.ofNat 64 idx)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD idx 0).toNat) (hh : VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s.mem hA) :
    WP isa (.block hbuSet) s fun s' =>
      VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s' ∧ s'.gpr .rax = BitVec.ofNat 64 (idx + 1) ∧
        VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s'.mem (huSet i ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD idx 0).toNat hA) ∧ Keep [.r8, .rax] s s' := by
  obtain ⟨hk4, hk8, -, -, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have hwr := hp.2.1
  have hb := ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD idx 0).isLt
  have ha : s.gpr .rcx + s.gpr .rsi * 4 = coeffAddr (s₀.gpr .rcx) (256 * i + ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD idx 0).toNat) := by
    rw [hP.rcx, hsi, VG.Proof.MlDsa.X86_64.Pack.setAddr]
  have hin : (VG.Proof.MlDsa.X86_64.Pack.uR s₀).Contains (coeffAddr (s₀.gpr .rcx) (256 * i + ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD idx 0).toNat)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuSet_ok s (by rw [hP.com.wr, hwr, ha]; exact ⟨_, List.mem_singleton_self _, hin⟩))
    fun s' ⟨⟨hm, hax'⟩, k'⟩ => ⟨hP.of_keep k' (by decide) ?_, by rw [hax', hax, VG.Proof.MlDsa.X86_64.Pack.ofNat_succ64], ?_, k'⟩
  · rw [hm, ha]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hin
  · rw [hm, ha]; exact VG.Proof.MlDsa.X86_64.Pack.harr_set hp hh hi hb

include hp in
/-- The first coefficient of polynomial `i`, from the index `first`. -/
theorem first_ok {i bound first : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.uk s₀) (hfb : first < bound) (hbω : bound ≤ VG.Proof.MlDsa.X86_64.Pack.uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s) (hax : s.gpr .rax = BitVec.ofNat 64 first)
    (hh : VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s.mem hA) :
    WP isa (.block (([.movzx8 .rsi (atIdx .rdi .rax)] : List Instr) ++ hbuSet ++
      ([.alu .cmp .rax (.reg .r11)] : List Instr))) s fun s' =>
      VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s' ∧ s'.gpr .rax = BitVec.ofNat 64 (first + 1) ∧
        VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s'.mem (huSet i ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD first 0).toNat hA) ∧
        s'.cf = some (decide (first + 1 < bound)) ∧ Keep [.r8, .rax, .rsi] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have hrd := hp.1
  have e1 : VG.Proof.MlDsa.X86_64.Pack.uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (WP.keep [.rsi] (Q := fun s' => s'.gpr .rsi = BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax)) ∧
    s'.mem = s.mem) (by
      xrun [VG.Proof.MlDsa.X86_64.Pack.ea_idx, show InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax) 1 by
        rw [hP.com.rd, hrd, hP.com.rdi, hax]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩])
    (by decide)) fun s₁ ⟨⟨si₁, m₁⟩, k₁⟩ => ?_
  have hb : s.mem (s.gpr .rdi + s.gpr .rax) = (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD first 0 := by
    rw [hP.com.rdi, hax]; exact VG.Proof.MlDsa.X86_64.Pack.yByte hp hP.com (by omega)
  have hP₁ : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s₁ := hP.of_keep k₁ (by decide) (by rw [m₁]; exact Frame.refl _ _)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.set_ok hp hi (idx := first) (hA := hA) hP₁ (by rw [k₁.gpr (by decide), hax])
    (by rw [si₁, hb]; apply BitVec.eq_of_toNat_eq; simp) (by rw [m₁]; exact hh)) fun s₂ ⟨hP₂, ax₂, hh₂, k₂⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ =>
    ⟨hP₂.of_keep k₃ (by decide) (by rw [m₃]; exact Frame.refl _ _), by rw [k₃.gpr (by decide), ax₂],
      by rw [m₃]; exact hh₂, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
  rw [cf₃, ax₂, hP₂.r11, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem hbuFail_ok (s : State) :
    WP isa hbuFail s fun s' => (s'.gpr .rax = 256 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

include hp in
/-- A coefficient after the first: checked against the previous one. -/
theorem next_ok {i bound first idx : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.uk s₀) (hfi : first < idx) (hib : idx < bound)
    (hbω : bound ≤ VG.Proof.MlDsa.X86_64.Pack.uω s₀) {hA : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s)
    (hax : s.gpr .rax = BitVec.ofNat 64 idx) (hh : VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s.mem hA) :
    WP isa hbuNext s fun s' => VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s' ∧
      (match huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first (hA, idx) 0 with
        | some (hA', idx') => s'.gpr .rax = BitVec.ofNat 64 idx' ∧ VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s'.mem hA' ∧
          s'.cf = some (decide (idx' < bound))
        | none => s'.gpr .rax = 256 ∧ s'.cf = some false) ∧ Keep [.r8, .rax, .rsi] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have hrd := hp.1
  have e1 : VG.Proof.MlDsa.X86_64.Pack.uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  have hprev : s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1) = s₀.gpr .rdi + BitVec.ofNat 64 (idx - 1) := by
    rw [hP.com.rdi, hax, VG.Proof.MlDsa.X86_64.Pack.ofNat_pred64 _ (by omega) (by omega)]
  have hcur : s.gpr .rdi + s.gpr .rax = s₀.gpr .rdi + BitVec.ofNat 64 idx := by rw [hP.com.rdi, hax]
  unfold hbuNext
  refine WP.seq (WP.mono (WP.keep [.r8, .rsi] (Q := fun s' =>
    s'.gpr .r8 = BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1))) ∧
    s'.gpr .rsi = BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax)) ∧
    s'.cf = some (decide ((BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1)))).toNat <
      (BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax))).toNat)) ∧ s'.mem = s.mem) (by
      xrun [VG.Proof.MlDsa.X86_64.Pack.ea_idx, VG.Proof.MlDsa.X86_64.Pack.ea_idxm1, show InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1)) 1 by
          rw [hP.com.rd, hrd, hprev]
          exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩,
        show InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax) 1 by
          rw [hP.com.rd, hrd, hcur]
          exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩])
    (by decide)) fun s₁ ⟨⟨r8₁, si₁, cf₁, m₁⟩, k₁⟩ => ?_)
  have hbp : s.mem (s.gpr .rdi + s.gpr .rax + BitVec.ofInt 64 (-1)) = (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (idx - 1) 0 := by
    rw [hprev]; exact VG.Proof.MlDsa.X86_64.Pack.yByte hp hP.com (by omega)
  have hbc : s.mem (s.gpr .rdi + s.gpr .rax) = (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD idx 0 := by
    rw [hcur]; exact VG.Proof.MlDsa.X86_64.Pack.yByte hp hP.com (by omega)
  have hP₁ : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s₁ := hP.of_keep k₁ (by decide) (by rw [m₁]; exact Frame.refl _ _)
  rw [hbp, hbc, toNat_setWidth64_8, toNat_setWidth64_8] at cf₁
  refine WP.seq ?_
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from cf₁) (fun hlt => ?_) (fun hge => ?_)
  · -- `y[index - 1] < y[index]`: set it.
    have hs : huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first (hA, idx) 0 = some (huSet i ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD idx 0).toNat hA, idx + 1) := by
      simp only [huStep]
      rw [ite_neg' (by simp only [decide_eq_true_eq] at hlt; omega)]
    rw [hs]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.set_ok hp hi (idx := idx) (hA := hA) hP₁ (by rw [k₁.gpr (by decide), hax])
      (by rw [si₁, hbc]; apply BitVec.eq_of_toNat_eq; simp) (by rw [m₁]; exact hh)) fun s₂ ⟨hP₂, ax₂, hh₂, k₂⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ =>
      ⟨hP₂.of_keep k₃ (by decide) (by rw [m₃]; exact Frame.refl _ _), ⟨by rw [k₃.gpr (by decide), ax₂],
        by rw [m₃]; exact hh₂, ?_⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    rw [cf₃, ax₂, hP₂.r11, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  · -- Not increasing: fail.
    have hs : huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first (hA, idx) 0 = none := by
      simp only [huStep]
      rw [ite_pos' (by simp only [decide_eq_false_iff_not] at hge; omega)]
    rw [hs]
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuFail_ok s₁) fun s₂ ⟨⟨ax₂, m₂⟩, k₂⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ =>
      ⟨hP₁.of_keep (k₂.trans k₃) (by decide) (by rw [m₃, m₂]; exact Frame.refl _ _),
        ⟨by rw [k₃.gpr (by decide), ax₂], ?_⟩, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    rw [cf₃, ax₂, k₂.gpr (by decide), hP₁.r11, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl,
      Nat.mod_eq_of_lt (by omega)]
    exact congrArg some (decide_eq_false (by omega))

/-- The state after the coefficients of a polynomial, up to the bound. -/
def SIn (s₀ : State) (bound : Nat) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => idx = bound ∧ s.gpr .rax = BitVec.ofNat 64 idx ∧ VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s.mem hA
  | none, s => s.gpr .rax = 256

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

include hp in
/-- The coefficients after the first. -/
theorem nexts_ok {i bound first : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.uk s₀) (hbω : bound ≤ VG.Proof.MlDsa.X86_64.Pack.uω s₀) {hA : Array (Vector Bool n)}
    {t : Nat} (ht1 : 1 ≤ t) {hA' : Array (Vector Bool n)} {idx' : Nat}
    (hF : optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range t) (hA, first) = some (hA', idx'))
    (hidx : idx' = first + t) (hlt : idx' < bound) {s : State} (hP : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s)
    (hax : s.gpr .rax = BitVec.ofNat 64 idx') (hh : VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s.mem hA') :
    WP isa (.loop hbuNext .b) s fun s' => VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s' ∧
      VG.Proof.MlDsa.X86_64.Pack.SIn s₀ bound (optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range (bound - first)) (hA, first)) s' ∧
      Keep [.r8, .rax, .rsi] s s' := by
  refine WP.loop (M := isa) (fun m s' => ∃ t hA' idx', m = bound - idx' ∧ 1 ≤ t ∧
      optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range t) (hA, first) = some (hA', idx') ∧ idx' = first + t ∧
      idx' < bound ∧ VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s' ∧ s'.gpr .rax = BitVec.ofNat 64 idx' ∧ VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s'.mem hA' ∧
      Keep [.r8, .rax, .rsi] s s')
    (fun m s' ⟨t, hA', idx', hm, ht1, hF, hidx, hlt, hP', hax', hh', hk'⟩ => ?_) _ s
    ⟨t, hA', idx', rfl, ht1, hF, hidx, hlt, hP, hax, hh, Keep.refl _ _⟩
  refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.next_ok hp hi (first := first) (by omega) hlt hbω hP' hax' hh') fun s'' ⟨hP'', hm'', hk''⟩ => ?_
  have hF1 : optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range (t + 1)) (hA, first) =
      huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first (hA', idx') t := by rw [optFold_range_succ, hF]; rfl
  cases hs : huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first (hA', idx') 0 with
  | none =>
    rw [hs] at hm''
    obtain ⟨ax'', cf''⟩ := hm''
    refine .inl ⟨cf'', hP'', ?_, (hk'.trans hk'').mono (by decide)⟩
    have : optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range (t + 1)) (hA, first) = none := by
      rw [hF1]; exact hs
    rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega) this]
    exact ax''
  | some st =>
    rw [hs] at hm''
    obtain ⟨hA'', idx''⟩ := st
    obtain ⟨ax'', hh'', cf''⟩ := hm''
    have hi'' : idx'' = idx' + 1 := VG.Proof.MlDsa.X86_64.Pack.huStep_idx hs
    have hF2 : optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range (t + 1)) (hA, first) = some (hA'', idx'') := by
      rw [hF1]; exact hs
    by_cases e : idx'' < bound
    · refine .inr ⟨by show s''.cf = _; rw [cf'', decide_eq_true e], bound - idx'', by omega, t + 1, hA'', idx'', rfl,
        by omega, hF2, by omega, e, hP'', ax'', hh'', (hk'.trans hk'').mono (by decide)⟩
    · refine .inl ⟨by show s''.cf = _; rw [cf'', decide_eq_false e], hP'', ?_, (hk'.trans hk'').mono (by decide)⟩
      rw [show bound - first = t + 1 by omega, hF2]
      exact ⟨by omega, ax'', hh''⟩

theorem cmpRegs_ok (s : State) :
    WP isa (.block [.alu .cmp .rax (.reg .r11)]) s fun s' =>
      (s'.cf = some (decide ((s.gpr .rax).toNat < (s.gpr .r11).toNat)) ∧ s'.mem = s.mem) ∧ Keep [] s s' :=
  VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .r11 s

include hp in
/-- The coefficients of polynomial `i`, from the index `first`, up to the bound. -/
theorem coefs_ok {i bound first : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ VG.Proof.MlDsa.X86_64.Pack.uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s) (hax : s.gpr .rax = BitVec.ofNat 64 first)
    (hh : VG.Proof.MlDsa.X86_64.Pack.HArr s₀ s.mem hA) :
    WP isa hbuCoefs s fun s' => VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s' ∧
      VG.Proof.MlDsa.X86_64.Pack.SIn s₀ bound (optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range (bound - first)) (hA, first)) s' ∧
      Keep [.r8, .rax, .rsi] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  unfold hbuCoefs
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpRegs_ok s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  have hP₁ : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i bound s₁ := hP.of_keep k₁ (by decide) (by rw [m₁]; exact Frame.refl _ _)
  rw [hax, hP.r11, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at cf₁
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from cf₁) (fun hlt => ?_) (fun hge => ?_)
  · -- The first coefficient, then the others.
    have hlt : first < bound := by simpa using hlt
    have hF1 : optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i first) (List.range 1) (hA, first) =
        some (huSet i ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD first 0).toNat hA, first + 1) := by
      simp only [List.range_one, optFold, huStep, gt_iff_lt, Nat.lt_irrefl, false_and, ite_false]; rfl
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.first_ok hp hi hlt hbω (hA := hA) hP₁ (by rw [k₁.gpr (by decide), hax]) (by rw [m₁]; exact hh))
      fun s₂ ⟨hP₂, ax₂, hh₂, cf₂, k₂⟩ => ?_)
    refine WP.ite (M := isa) _ (show isa.eval .b s₂ = _ from cf₂) (fun hlt₂ => ?_) (fun hge₂ => ?_)
    · have hlt₂ : first + 1 < bound := by simpa using hlt₂
      exact WP.mono (VG.Proof.MlDsa.X86_64.Pack.nexts_ok hp hi hbω (Nat.le_refl 1) hF1 rfl hlt₂ hP₂ ax₂ hh₂) fun s₃ ⟨hP₃, hr₃, k₃⟩ =>
        ⟨hP₃, hr₃, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · have hge₂ : ¬ first + 1 < bound := by simpa using hge₂
      refine WP.block_nil ⟨hP₂, ?_, (k₁.trans k₂).mono (by decide)⟩
      rw [show bound - first = 1 by omega, hF1]
      exact ⟨by omega, ax₂, hh₂⟩
  · -- No coefficient.
    have hge : ¬ first < bound := by simpa using hge
    refine WP.block_nil ⟨hP₁, ?_, k₁.mono (by decide)⟩
    rw [show bound - first = 0 by omega]
    exact ⟨by omega, by rw [k₁.gpr (by decide), hax], by rw [m₁]; exact hh⟩

/-- The spec's state after `i` polynomials. -/
abbrev huS (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (VG.Proof.MlDsa.X86_64.Pack.uω s₀) (VG.Proof.MlDsa.X86_64.Pack.uY s₀)) (List.range i) (Array.replicate (VG.Proof.MlDsa.X86_64.Pack.uk s₀) noHint, 0)

/-- Before polynomial `i`. -/
structure OInv (s₀ : State) (i : Nat) (s : State) : Prop where
  com : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s
  r9 : s.gpr .r9 = s₀.gpr .rdi + BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i)
  rcx : s.gpr .rcx = s₀.gpr .rcx + BitVec.ofNat 64 (1024 * i)
  st : VG.Proof.MlDsa.X86_64.Pack.SRel s₀ (VG.Proof.MlDsa.X86_64.Pack.huS s₀ i) s

theorem bound_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .r9) 1) :
    WP isa (.block [.movzx8 .r11 (VG.Impl.MlDsa.X86_64.Pack.at_ .r9 0), .alu .cmp .r11 (.reg .rax)]) s fun s' =>
      (s'.gpr .r11 = BitVec.setWidth 64 (s.mem (s.gpr .r9)) ∧
        s'.cf = some (decide ((s.mem (s.gpr .r9)).toNat < (s.gpr .rax).toNat)) ∧ s'.mem = s.mem) ∧
        Keep [.r11] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [ea_at', hin, toNat_setWidth64_8]

theorem polyTail_ok (s : State) :
    WP isa (.block [.alu .add .r9 (.imm 1), .alu .add .rcx (.imm 1024), .alu .sub .r10 (.imm 1)]) s fun s' =>
      (s'.gpr .r9 = s.gpr .r9 + 1 ∧ s'.gpr .rcx = s.gpr .rcx + 1024 ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧
        s'.zf = some (s.gpr .r10 - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.r9, .rcx, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [show BitVec.signExtend 64 (1024 : BitVec 32) = 1024 by decide]

include hp in
/-- Polynomial `i`: its checks and coefficients, unless a check failed. -/
theorem upoly_ok {i : Nat} (hi : i < VG.Proof.MlDsa.X86_64.Pack.uk s₀) {s : State} (hI : VG.Proof.MlDsa.X86_64.Pack.OInv s₀ i s) :
    WP isa (.seq hbuPoly (.block [.alu .add .r9 (.imm 1), .alu .add .rcx (.imm 1024), .alu .sub .r10 (.imm 1)])) s
      fun s' => VG.Proof.MlDsa.X86_64.Pack.OInv s₀ (i + 1) s' ∧ s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0) ∧
        Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have hrd := hp.1
  have e1 : VG.Proof.MlDsa.X86_64.Pack.uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  have hsucc : VG.Proof.MlDsa.X86_64.Pack.huS s₀ (i + 1) = (VG.Proof.MlDsa.X86_64.Pack.huS s₀ i).bind fun st => huPoly (VG.Proof.MlDsa.X86_64.Pack.uω s₀) (VG.Proof.MlDsa.X86_64.Pack.uY s₀) st i := optFold_range_succ _ _ _
  have hωeq : VG.Proof.MlDsa.X86_64.Pack.uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [VG.Proof.MlDsa.X86_64.Pack.uω, dArg]
  -- After the polynomial, whichever way it went.
  suffices h : WP isa hbuPoly s fun s' => VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s' ∧ s'.gpr .r9 = s.gpr .r9 ∧ s'.gpr .rcx = s.gpr .rcx ∧
      s'.gpr .r10 = s.gpr .r10 ∧ VG.Proof.MlDsa.X86_64.Pack.SRel s₀ (VG.Proof.MlDsa.X86_64.Pack.huS s₀ (i + 1)) s' ∧ Keep [.rax, .rsi, .r8, .r11] s s' by
    refine WP.seq (WP.mono h fun s₁ ⟨hc₁, r9₁, cx₁, r10₁, st₁, k₁⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.polyTail_ok s₁) fun s₂ ⟨⟨r9₂, cx₂, r10₂, z₂, m₂⟩, k₂⟩ => ⟨⟨hc₁.of_keep k₂ (by decide) (by decide)
      (by rw [m₂]; exact Frame.refl _ _), ?_, ?_, ?_⟩, by rw [r10₂, r10₁], by rw [z₂, r10₁],
      (k₁.trans k₂).mono (by decide)⟩
    · rw [r9₂, r9₁, hI.r9, BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_add_ofNat, Nat.add_assoc]
    · rw [cx₂, cx₁, hI.rcx, BitVec.add_assoc, show (1024 : BitVec 64) = BitVec.ofNat 64 1024 from rfl,
        BitVec.ofNat_add_ofNat, show 1024 * i + 1024 = 1024 * (i + 1) by omega]
    · -- `rax` and the memory of `h`: `SRel` does not look at the other registers.
      revert st₁
      cases VG.Proof.MlDsa.X86_64.Pack.huS s₀ (i + 1) with
      | none => exact fun h => by rw [VG.Proof.MlDsa.X86_64.Pack.SRel] at h ⊢; rw [k₂.gpr (by decide), h]
      | some st => obtain ⟨hA, idx⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨by rw [k₂.gpr (by decide), h1], h2, by rw [m₂]; exact h3⟩
  unfold hbuPoly
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rdx .rax s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  have hc₁ : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s₁ := hI.com.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
  cases hS : VG.Proof.MlDsa.X86_64.Pack.huS s₀ i with
  | none =>
    -- A check failed before: nothing.
    have hax : s.gpr .rax = 256 := by have := hI.st; rw [hS] at this; exact this
    rw [hI.com.rdx, hax, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl, Nat.mod_eq_of_lt (by omega)]
      at cf₁
    refine WP.ite (M := isa) false (by show Option.map _ s₁.cf = _; rw [cf₁]; simp; omega) (fun h => by cases h)
      fun _ => WP.block_nil ⟨hc₁, k₁.gpr (by decide), k₁.gpr (by decide), k₁.gpr (by decide), ?_, k₁.mono (by decide)⟩
    rw [hsucc, hS]
    exact (k₁.gpr (by decide)).trans hax
  | some st =>
    obtain ⟨hA, idx⟩ := st
    have hst := hI.st
    rw [hS] at hst
    obtain ⟨hax, hidx, hh⟩ := hst
    rw [hI.com.rdx, hax, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at cf₁
    refine WP.ite (M := isa) true (by show Option.map _ s₁.cf = _; rw [cf₁]; simp; omega) (fun _ => ?_)
      (fun h => by cases h)
    -- The bound.
    have hr9 : s₁.gpr .r9 = s₀.gpr .rdi + BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) := (k₁.gpr (by decide)).trans hI.r9
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.bound_ok s₁ (by
        rw [hc₁.rd, hc₁.wr, hrd, hr9]
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨⟨r11₂, cf₂, m₂⟩, k₂⟩ => ?_)
    have hbd : s₁.mem (s₁.gpr .r9) = (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0 := by rw [hr9]; exact VG.Proof.MlDsa.X86_64.Pack.yByte hp hc₁ (by omega)
    have hc₂ : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s₂ := hc₁.of_keep k₂ (by decide) (by decide) (by rw [m₂]; exact Frame.refl _ _)
    have hbl := ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0).isLt
    rw [hbd, k₁.gpr (by decide), hax, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at cf₂
    have hpoly := hsucc
    rw [hS] at hpoly
    simp only [Option.bind_some, huPoly] at hpoly
    refine WP.ite (M := isa) _ (show isa.eval .b s₂ = _ from cf₂) (fun hlt => ?_) (fun hge => ?_)
    · -- `bound < index`: fail.
      have hlt : ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0).toNat < idx := by simpa using hlt
      refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuFail_ok s₂) fun s₃ ⟨⟨ax₃, m₃⟩, k₃⟩ => ⟨hc₂.of_keep k₃ (by decide) (by decide)
        (by rw [m₃]; exact Frame.refl _ _), ?_, ?_, ?_, ?_, ((k₁.trans k₂).trans k₃).mono (by decide)⟩
      · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
      · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
      · rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
      · rw [hpoly, ite_pos' (.inl hlt)]; exact ax₃
    · have hge : ¬ ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0).toNat < idx := by simpa using hge
      refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rdx .r11 s₂) fun s₃ ⟨⟨cf₃, m₃⟩, k₃⟩ => ?_)
      have hc₃ : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s₃ := hc₂.of_keep k₃ (by decide) (by decide) (by rw [m₃]; exact Frame.refl _ _)
      rw [hc₂.rdx, r11₂, hbd, toNat_setWidth64_8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at cf₃
      refine WP.ite (M := isa) _ (show isa.eval .b s₃ = _ from cf₃) (fun hgt => ?_) (fun hle => ?_)
      · -- `bound > ω`: fail.
        have hgt : VG.Proof.MlDsa.X86_64.Pack.uω s₀ < ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0).toNat := by simpa using hgt
        refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuFail_ok s₃) fun s₄ ⟨⟨ax₄, m₄⟩, k₄⟩ => ⟨hc₃.of_keep k₄ (by decide) (by decide)
          (by rw [m₄]; exact Frame.refl _ _), ?_, ?_, ?_, ?_, (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [hpoly, ite_pos' (.inr hgt)]; exact ax₄
      · -- The coefficients.
        have hle : ¬ VG.Proof.MlDsa.X86_64.Pack.uω s₀ < ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0).toNat := by simpa using hle
        have hP₃ : VG.Proof.MlDsa.X86_64.Pack.PCom s₀ i ((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0).toNat s₃ :=
          ⟨hc₃, by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hI.rcx],
            by rw [k₃.gpr (by decide), r11₂, hbd]; apply BitVec.eq_of_toNat_eq; simp⟩
        refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.coefs_ok hp hi (first := idx) (hA := hA) (by omega) (by omega) hP₃
          (by rw [k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide), hax])
          (by rw [m₃, m₂, m₁]; exact hh)) fun s₄ ⟨hP₄, hin₄, k₄⟩ => ⟨hP₄.com, ?_, ?_, ?_, ?_,
            (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [hP₄.rcx, hI.rcx]
        · rw [k₄.gpr (by decide), k₃.gpr (by decide), k₂.gpr (by decide), k₁.gpr (by decide)]
        · rw [hpoly, ite_neg' (by omega)]
          revert hin₄
          cases optFold (huStep (VG.Proof.MlDsa.X86_64.Pack.uY s₀) i idx) (List.range (((VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (VG.Proof.MlDsa.X86_64.Pack.uω s₀ + i) 0).toNat - idx)) (hA, idx) with
          | none => exact id
          | some st => obtain ⟨hA', idx'⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨h2, by omega, h3⟩

/-! ## The bytes after the last index -/

theorem trailLoad_ok (s : State) (hin : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rax) 1) :
    WP isa (.block [.movzx8 .r8 (atIdx .rdi .rax), .alu32 .cmp .r8 (.imm 0)]) s fun s' =>
      (s'.zf = some (BitVec.setWidth 32 (BitVec.setWidth 64 (s.mem (s.gpr .rdi + s.gpr .rax))) - 0 == 0) ∧
        s'.mem = s.mem) ∧ Keep [.r8] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [VG.Proof.MlDsa.X86_64.Pack.ea_idx, hin]

theorem incRax_ok (s : State) :
    WP isa (.block [.alu .add .rax (.imm 1)]) s fun s' =>
      (s'.gpr .rax = s.gpr .rax + 1 ∧ s'.mem = s.mem) ∧ Keep [.rax] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem byte_ne_zero (b : Byte) :
    (BitVec.setWidth 32 (BitVec.setWidth 64 b) - 0 == 0) = decide (b = 0) := by
  rw [VG.Proof.MlKem.X86_64.sub_beq_zero32]
  simp only [decide_eq_decide]
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    have h2 := b.isLt
    simp only [BitVec.toNat_setWidth] at h1
    rw [show (0 : BitVec 32).toNat = 0 from rfl] at h1
    apply BitVec.eq_of_toNat_eq
    rw [show (0 : Byte).toNat = 0 from rfl]
    omega
  · intro h; rw [h]; rfl

include hp in
/-- The bytes from the index `idx` up to `ω`. -/
theorem trail_ok {idx : Nat} (hidx : idx ≤ VG.Proof.MlDsa.X86_64.Pack.uω s₀) {s : State} (hc : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s)
    (hax : s.gpr .rax = BitVec.ofNat 64 idx) :
    WP isa hbuTrail s fun s' => VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s' ∧ s'.mem = s.mem ∧
      (match optFold (huTrail (VG.Proof.MlDsa.X86_64.Pack.uY s₀)) (List.range' idx (VG.Proof.MlDsa.X86_64.Pack.uω s₀ - idx)) () with
        | some _ => s'.gpr .rax = BitVec.ofNat 64 (VG.Proof.MlDsa.X86_64.Pack.uω s₀)
        | none => s'.gpr .rax = 256) ∧ Keep [.rax, .r8] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have hrd := hp.1
  have e1 : VG.Proof.MlDsa.X86_64.Pack.uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have hl := (s₀.gpr .rsi).isLt
  have hωeq : VG.Proof.MlDsa.X86_64.Pack.uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [VG.Proof.MlDsa.X86_64.Pack.uω, dArg]
  unfold hbuTrail
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .rdx s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  have hc₁ : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s₁ := hc.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _)
  rw [hax, hc.rdx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)] at cf₁
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from cf₁) (fun hlt => ?_) (fun hge => ?_)
  · have hlt : idx < VG.Proof.MlDsa.X86_64.Pack.uω s₀ := by simpa using hlt
    refine WP.loop (M := isa) (fun m s' => ∃ u, m = VG.Proof.MlDsa.X86_64.Pack.uω s₀ - idx - u ∧ idx + u < VG.Proof.MlDsa.X86_64.Pack.uω s₀ ∧
        optFold (huTrail (VG.Proof.MlDsa.X86_64.Pack.uY s₀)) (List.range' idx u) () = some () ∧ s'.gpr .rax = BitVec.ofNat 64 (idx + u) ∧
        VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s' ∧ s'.mem = s.mem ∧ Keep [.rax, .r8] s s')
      (fun m s' ⟨u, hm, hu, hF, hax', hc', hm', hk'⟩ => ?_) _ s₁
      ⟨0, rfl, by omega, rfl, by rw [k₁.gpr (by decide), hax]; rfl, hc₁, m₁, k₁.mono (by decide)⟩
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.trailLoad_ok s' (by
        rw [hc'.rd, hc'.wr, hrd, hc'.rdi, hax']
        exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), Offset.contains_base _ (by omega) (by omega)⟩))
      fun s₂ ⟨⟨z₂, m₂⟩, k₂⟩ => ?_)
    have hbyte : s'.mem (s'.gpr .rdi + s'.gpr .rax) = (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (idx + u) 0 := by
      rw [hc'.rdi, hax']; exact VG.Proof.MlDsa.X86_64.Pack.yByte hp hc' (by omega)
    rw [hbyte, VG.Proof.MlDsa.X86_64.Pack.byte_ne_zero] at z₂
    have hc₂ : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s₂ := hc'.of_keep k₂ (by decide) (by decide) (by rw [m₂]; exact Frame.refl _ _)
    have hF1 : optFold (huTrail (VG.Proof.MlDsa.X86_64.Pack.uY s₀)) (List.range' idx (u + 1)) () =
        huTrail (VG.Proof.MlDsa.X86_64.Pack.uY s₀) () (idx + u) := by rw [optFold_range'_succ, hF]; rfl
    refine WP.seq ?_
    refine WP.ite (M := isa) _ (show Option.map _ s₂.zf = _ by rw [z₂]; rfl) (fun hne => ?_) (fun heq => ?_)
    · -- A nonzero byte: fail.
      have hne : (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (idx + u) 0 ≠ 0 := by simpa using hne
      have hn : optFold (huTrail (VG.Proof.MlDsa.X86_64.Pack.uY s₀)) (List.range' idx (VG.Proof.MlDsa.X86_64.Pack.uω s₀ - idx)) () = none :=
        optFold_range'_none _ _ (show u + 1 ≤ VG.Proof.MlDsa.X86_64.Pack.uω s₀ - idx by omega) (by rw [hF1, huTrail, ite_pos' hne])
      refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuFail_ok s₂) fun s₃ ⟨⟨ax₃, m₃⟩, k₃⟩ => ?_
      refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .rdx s₃) fun s₄ ⟨⟨cf₄, m₄⟩, k₄⟩ => .inl ⟨?_, ⟨hc₂.of_keep (k₃.trans k₄) (by decide)
        (by decide) (by rw [m₄, m₃]; exact Frame.refl _ _), by rw [m₄, m₃, m₂, hm'], ?_,
        (((hk'.trans k₂).trans k₃).trans k₄).mono (by decide)⟩⟩
      · show s₄.cf = _
        rw [cf₄, ax₃, k₃.gpr (by decide), hc₂.rdx, show (256 : BitVec 64).toNat = 256 from rfl, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
        exact congrArg some (decide_eq_false (by omega))
      · rw [hn]; exact (k₄.gpr (by decide)).trans ax₃
    · -- A zero byte: next.
      have heq : (VG.Proof.MlDsa.X86_64.Pack.uY s₀).getD (idx + u) 0 = 0 := by simpa using heq
      have hF2 : optFold (huTrail (VG.Proof.MlDsa.X86_64.Pack.uY s₀)) (List.range' idx (u + 1)) () = some () := by
        rw [hF1, huTrail, ite_neg' (by simpa using heq)]
      refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.incRax_ok s₂) fun s₃ ⟨⟨ax₃, m₃⟩, k₃⟩ => ?_
      have ax₃' : s₃.gpr .rax = BitVec.ofNat 64 (idx + (u + 1)) := by
        rw [ax₃, k₂.gpr (by decide), hax', VG.Proof.MlDsa.X86_64.Pack.ofNat_succ64, Nat.add_assoc]
      refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .rdx s₃) fun s₄ ⟨⟨cf₄, m₄⟩, k₄⟩ => ?_
      have hc₄ : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s₄ := hc₂.of_keep (k₃.trans k₄) (by decide) (by decide) (by rw [m₄, m₃]; exact Frame.refl _ _)
      rw [ax₃', k₃.gpr (by decide), hc₂.rdx, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at cf₄
      have ax₄ : s₄.gpr .rax = BitVec.ofNat 64 (idx + (u + 1)) := (k₄.gpr (by decide)).trans ax₃'
      by_cases e : idx + (u + 1) < VG.Proof.MlDsa.X86_64.Pack.uω s₀
      · exact .inr ⟨by show s₄.cf = _; rw [cf₄, decide_eq_true e], _, by omega, u + 1, rfl, e, hF2, ax₄, hc₄,
          by rw [m₄, m₃, m₂, hm'], (((hk'.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
      · refine .inl ⟨by show s₄.cf = _; rw [cf₄, decide_eq_false e], hc₄, by rw [m₄, m₃, m₂, hm'], ?_,
          (((hk'.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
        rw [show VG.Proof.MlDsa.X86_64.Pack.uω s₀ - idx = u + 1 by omega, hF2]
        rw [ax₄, show idx + (u + 1) = VG.Proof.MlDsa.X86_64.Pack.uω s₀ by omega]
  · -- `idx = ω`: nothing.
    have hge : ¬ idx < VG.Proof.MlDsa.X86_64.Pack.uω s₀ := by simpa using hge
    refine WP.block_nil ⟨hc₁, m₁, ?_, k₁.mono (by decide)⟩
    rw [show VG.Proof.MlDsa.X86_64.Pack.uω s₀ - idx = 0 by omega]
    simp only [List.range'_zero, optFold]
    rw [k₁.gpr (by decide), hax, show idx = VG.Proof.MlDsa.X86_64.Pack.uω s₀ by omega]

include hp in
theorem trail_fail {s : State} (hc : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s) (hax : s.gpr .rax = 256) :
    WP isa hbuTrail s fun s' => VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .rax = 256 ∧ Keep [.rax, .r8] s s' := by
  obtain ⟨-, -, hω80, -, -⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have hωeq : VG.Proof.MlDsa.X86_64.Pack.uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [VG.Proof.MlDsa.X86_64.Pack.uω, dArg]
  unfold hbuTrail
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.cmpReg_ok .rax .rdx s) fun s₁ ⟨⟨cf₁, m₁⟩, k₁⟩ => ?_)
  rw [hax, hc.rdx, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl, Nat.mod_eq_of_lt (by omega)] at cf₁
  refine WP.ite (M := isa) false (by show s₁.cf = _; rw [cf₁]; exact congrArg some (decide_eq_false (by omega)))
    (fun h => by cases h) fun _ => WP.block_nil ⟨hc.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _),
      m₁, (k₁.gpr (by decide)).trans hax, k₁.mono (by decide)⟩

/-! ## The function -/

theorem hbuSetup_ok (s : State) :
    WP isa (.block [.mov .r9 (.reg .rdi), .alu .add .r9 (.reg .rdx), .mov .r10 (.reg .rsi), .alu .sub .r10 (.reg .rdx)])
      s fun s' => (s'.gpr .r9 = s.gpr .rdi + s.gpr .rdx ∧ s'.gpr .r10 = s.gpr .rsi - s.gpr .rdx ∧ s'.mem = s.mem) ∧
        Keep [.r9, .r10] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem hbuRet_ok (s : State) :
    WP isa (.block hbuRet) s fun s' =>
      (BitVec.setWidth 32 (s'.gpr .rax) = if (s.gpr .rdx).toNat < (s.gpr .rax).toNat then 0 else 1) ∧ s'.mem = s.mem := by
  unfold hbuRet
  xrun
  split
  · rename_i h; rw [decide_eq_true h]; rfl
  · rename_i h; rw [decide_eq_false h]; rfl

include hp in
/-- The polynomials. -/
theorem hbuMain_ok {s : State} (hc : VG.Proof.MlDsa.X86_64.Pack.UCom s₀ s) (hax : s.gpr .rax = 0)
    (hz : ∀ t < (s₀.gpr .r8).toNat, coeffAt s.mem (s₀.gpr .rcx) t = 0) (hcx : s.gpr .rcx = s₀.gpr .rcx)
    (hsi : s.gpr .rsi = s₀.gpr .rsi) :
    WP isa hbuMain s fun s' => VG.Proof.MlDsa.X86_64.Pack.OInv s₀ (VG.Proof.MlDsa.X86_64.Pack.uk s₀) s' ∧ Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have e1 : VG.Proof.MlDsa.X86_64.Pack.uLen s₀ = (s₀.gpr .rsi).toNat := rfl
  have e2 : VG.Proof.MlDsa.X86_64.Pack.uk s₀ = (s₀.gpr .rsi).toNat - VG.Proof.MlDsa.X86_64.Pack.uω s₀ := rfl
  have hωeq : VG.Proof.MlDsa.X86_64.Pack.uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [VG.Proof.MlDsa.X86_64.Pack.uω, dArg]
  unfold hbuMain
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuSetup_ok s) fun s₁ ⟨⟨r9₁, r10₁, m₁⟩, k₁⟩ => ?_)
  refine WP.mono (wp_countdown (cnt := .r10) (N := VG.Proof.MlDsa.X86_64.Pack.uk s₀) (by omega) (by omega)
    (fun i s' => VG.Proof.MlDsa.X86_64.Pack.OInv s₀ i s' ∧ Keep [.rax, .rcx, .rsi, .r8, .r9, .r10, .r11] s s')
    (fun i hi s' ⟨hI, hk⟩ _ => WP.mono (VG.Proof.MlDsa.X86_64.Pack.upoly_ok hp hi hI) fun s'' ⟨hI', h10, hz', hk'⟩ =>
      ⟨⟨hI', (hk.trans hk').mono (by decide)⟩, h10, hz'⟩)
    (fun s' h => h) (s := s₁) ⟨⟨hc.of_keep k₁ (by decide) (by decide) (by rw [m₁]; exact Frame.refl _ _), ?_, ?_, ?_⟩,
      k₁.mono (by decide)⟩ ?_) fun s' h => h
  · rw [r9₁, hc.rdi, hc.rdx]; rfl
  · rw [k₁.gpr (by decide), hcx]; simp
  · show VG.Proof.MlDsa.X86_64.Pack.SRel s₀ (some (Array.replicate (VG.Proof.MlDsa.X86_64.Pack.uk s₀) noHint, 0)) s₁
    exact ⟨by rw [k₁.gpr (by decide), hax]; rfl, Nat.zero_le _, by rw [m₁]; exact VG.Proof.MlDsa.X86_64.Pack.harr_zero hp hz⟩
  · rw [r10₁, hsi, hc.rdx]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := (s₀.gpr .rsi).isLt
    omega

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {m : Mem} {hA : Array (Vector Bool n)} (hh : VG.Proof.MlDsa.X86_64.Pack.HArr s₀ m hA) :
    HintIs m (s₀.gpr .rcx) (VG.Proof.MlDsa.X86_64.Pack.uk s₀) hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

include hp in
theorem hbu_wp :
    WP isa Impl.MlDsa.X86_64.Pack.hintBitUnpack s₀ fun s' =>
      hintBitUnpackK.post s₀ s' ∧ Frame [VG.Proof.MlDsa.X86_64.Pack.uR s₀] s₀.mem s'.mem := by
  obtain ⟨hk4, hk8, hω80, hsum, hr8⟩ := VG.Proof.MlDsa.X86_64.Pack.up_facts hp
  have hωeq : VG.Proof.MlDsa.X86_64.Pack.uω s₀ = (s₀.gpr .rdx).toNat % 2 ^ 32 := by simp [VG.Proof.MlDsa.X86_64.Pack.uω, dArg]
  unfold Impl.MlDsa.X86_64.Pack.hintBitUnpack
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuZero_ok hp) fun s₁ ⟨hz₁, hf₁, ax₁, dx₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuMain_ok hp (s := s₁) ⟨k₁.gpr (by decide), dx₁, k₁.2.1, k₁.2.2, hf₁⟩ ax₁ hz₁
    (k₁.gpr (by decide)) (k₁.gpr (by decide))) fun s₂ ⟨hI, k₂⟩ => ?_)
  -- The spec, as folds.
  show WP isa _ s₂ fun s' => (match hintBitUnpack (VG.Proof.MlDsa.X86_64.Pack.uω s₀) (VG.Proof.MlDsa.X86_64.Pack.uk s₀) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat) with
    | some hint => BitVec.setWidth 32 (s'.gpr .rax) = 1 ∧ HintIs s'.mem (s₀.gpr .rcx) (VG.Proof.MlDsa.X86_64.Pack.uk s₀) hint
    | none => BitVec.setWidth 32 (s'.gpr .rax) = 0) ∧ Frame [VG.Proof.MlDsa.X86_64.Pack.uR s₀] s₀.mem s'.mem
  rw [hintBitUnpack_eq]
  have hst := hI.st
  cases hS : VG.Proof.MlDsa.X86_64.Pack.huS s₀ (VG.Proof.MlDsa.X86_64.Pack.uk s₀) with
  | none =>
    rw [hS] at hst
    rw [show optFold (huPoly (VG.Proof.MlDsa.X86_64.Pack.uω s₀) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat).toArray)
      (List.range (VG.Proof.MlDsa.X86_64.Pack.uk s₀)) (Array.replicate (VG.Proof.MlDsa.X86_64.Pack.uk s₀) noHint, 0) = none from hS]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.trail_fail hp hI.com hst) fun s₃ ⟨hc₃, m₃, ax₃, k₃⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuRet_ok s₃) fun s₄ ⟨ax₄, m₄⟩ => ⟨?_, by rw [m₄, m₃]; exact hI.com.frame⟩
    rw [ax₄, ax₃, hc₃.rdx, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl, Nat.mod_eq_of_lt (by omega),
      ite_pos' (by omega)]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hS] at hst
    obtain ⟨hax, hidx, hh⟩ := hst
    rw [show optFold (huPoly (VG.Proof.MlDsa.X86_64.Pack.uω s₀) (bytesAt s₀.mem (s₀.gpr .rdi) (s₀.gpr .rsi).toNat).toArray)
      (List.range (VG.Proof.MlDsa.X86_64.Pack.uk s₀)) (Array.replicate (VG.Proof.MlDsa.X86_64.Pack.uk s₀) noHint, 0) = some (hA, idx) from hS]
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Pack.trail_ok hp hidx hI.com hax) fun s₃ ⟨hc₃, m₃, hr₃, k₃⟩ => ?_)
    refine WP.mono (VG.Proof.MlDsa.X86_64.Pack.hbuRet_ok s₃) fun s₄ ⟨ax₄, m₄⟩ => ⟨?_, by rw [m₄, m₃]; exact hI.com.frame⟩
    dsimp only
    revert hr₃
    cases optFold (huTrail (VG.Proof.MlDsa.X86_64.Pack.uY s₀)) (List.range' idx (VG.Proof.MlDsa.X86_64.Pack.uω s₀ - idx)) () with
    | none =>
      intro hr₃
      rw [ax₄, hr₃, hc₃.rdx, BitVec.toNat_ofNat, show (256 : BitVec 64).toNat = 256 from rfl,
        Nat.mod_eq_of_lt (by omega), ite_pos' (by omega)]
      rfl
    | some _ =>
      intro hr₃
      refine ⟨?_, by rw [m₄, m₃]; exact VG.Proof.MlDsa.X86_64.Pack.harr_hintIs hh⟩
      rw [ax₄, hr₃, hc₃.rdx, ite_neg' (Nat.lt_irrefl _)]

end

theorem hintBitUnpack_correct (s : State) (hs : hintBitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.X86_64.Pack.hintBitUnpack s t s' ∧ abiPreserved s s' ∧ hintBitUnpackK.post s s' := by
  obtain ⟨t, s', he, ⟨hb, hf⟩, hk⟩ := WP.keep (c := Impl.MlDsa.X86_64.Pack.hintBitUnpack)
    [.rax, .rcx, .rdx, .rsi, .r8, .r9, .r10, .r11] (VG.Proof.MlDsa.X86_64.Pack.hbu_wp hs) (by decide)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf
    (by simpa using hs.2.2.2.2.1)), hb⟩

/-! ## Constant time -/

/-- A byte of the words of a region of zero words. -/
theorem byte_of_zero_words {m : Mem} {p : Addr} {N : Nat} (hz : ∀ t < N, coeffAt m p t = 0) {a : Addr}
    (ha : (⟨p, N * 4⟩ : Region).Contains a 1) : m a = 0 := by
  simp only [Region.Contains] at ha
  have ht : (a - p).toNat % 4 < 4 := Nat.mod_lt _ (by decide)
  have ea : a = coeffAddr p ((a - p).toNat / 4) + BitVec.ofNat 64 ((a - p).toNat % 4) := by
    rw [coeffAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.div_add_mod, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [ea, Mem.readW_byte m (coeffAddr p _) ht, ← coeffAt_eq, hz _ (by omega)]
  simp

theorem map_toNat_inj : ∀ {b₁ b₂ : List Byte}, b₁.map (·.toNat) = b₂.map (·.toNat) → b₁ = b₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.X86_64.Pack.map_toNat_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The taint of the loops: the pointers, the lengths, `ω` and the index. -/
abbrev hbuTaint : X86_64.Taint.T := X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rax]

theorem hintBitUnpack_ct :
    ConstantTime isa hintBitUnpackK.pre hintBitUnpackK.pub Impl.MlDsa.X86_64.Pack.hintBitUnpack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := VG.Proof.MlDsa.X86_64.Pack.MAgree VG.Proof.MlDsa.X86_64.Pack.hbuTaint) ?_ (RelCT.taint (A := VG.Proof.MlDsa.X86_64.Pack.memTaint) VG.Proof.MlDsa.X86_64.Pack.hbuTaint (fun _ _ h => h) (by taint_decide))
  refine Proof.MlKem.X86_64.RelCT.postDep
    (RelCT.taint (A := taint) (regsLo [.rdi, .rsi, .rcx, .r8, .rsp] [.rdx])
      (fun _ _ ⟨_, _, hp⟩ => agree_regsLo (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1])
        fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; exact hp.2.2.2.2.2.1)
      (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨VG.Proof.MlDsa.X86_64.Pack.hbuZero_ok hx, VG.Proof.MlDsa.X86_64.Pack.hbuZero_ok hy⟩) fun x y x' y' ⟨hx, hy, hp⟩ fx fy => ?_
  obtain ⟨hz₁, hf₁, ax₁, dx₁, k₁⟩ := fx
  obtain ⟨hz₂, hf₂, ax₂, dx₂, k₂⟩ := fy
  obtain ⟨di, si, ci, r8, -, dx, hleak⟩ := hp
  have hdx : dArg x .rdx = dArg y .rdx := by unfold dArg; rw [dx]
  have hrd : x'.rd = y'.rd := by rw [k₁.2.1, k₂.2.1, hx.1, hy.1, di, si]
  have hwr : x'.wr = y'.wr := by rw [k₁.2.2, k₂.2.2, hx.2.1, hy.2.1, ci, r8]
  refine ⟨X86_64.Taint.agree_ofRegs fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), di]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), si]
    · rw [dx₁, dx₂]; exact congrArg _ hdx
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), ci]
    · rw [k₁.gpr (by decide), k₂.gpr (by decide), r8]
    · rw [ax₁, ax₂]
  · rw [k₁.2.1, k₁.2.2, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- `y`: as on entry, where the runs agree.
      have hdis : ∀ r ∈ [VG.Proof.MlDsa.X86_64.Pack.uR x], ¬ r.Contains a 1 := by
        intro r hr hc'; simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'
      rw [hf₁ a hdis, hf₂ a (fun r hr hc' => by
        simp only [List.mem_singleton] at hr; subst hr
        simp only [VG.Proof.MlDsa.X86_64.Pack.uR, ← ci, ← r8] at hc'
        exact hx.2.2.1 a hc hc')]
      have hlt : (a - x.gpr .rdi).toNat < (x.gpr .rsi).toNat := by simp only [Region.Contains] at hc; omega
      have ea : a = x.gpr .rdi + BitVec.ofNat 64 (a - x.gpr .rdi).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hb : bytesAt x.mem (x.gpr .rdi) (x.gpr .rsi).toNat = bytesAt y.mem (x.gpr .rdi) (x.gpr .rsi).toNat := by
        have hl2 := hleak
        rw [← di, ← si] at hl2
        exact VG.Proof.MlDsa.X86_64.Pack.map_toNat_inj hl2
      have h₁ := congrArg (·.getD (a - x.gpr .rdi).toNat 0) hb
      rw [bytesAt_getD _ _ hlt, bytesAt_getD _ _ hlt, ← ea] at h₁
      exact h₁
    · -- `h`: zeros.
      rw [VG.Proof.MlDsa.X86_64.Pack.byte_of_zero_words hz₁ hc, VG.Proof.MlDsa.X86_64.Pack.byte_of_zero_words hz₂ (by rw [← ci, ← r8]; exact hc)]

/-- A state satisfying the precondition. -/
def hintBitUnpackSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 84 | .rdx => 80 | .rcx => 0x3000 | .r8 => 1024 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 84⟩]
  wr := [⟨0x3000, 4096⟩]

theorem hintBitUnpack_verified :
    Verified X86_64.target Impl.MlDsa.X86_64.Pack.hintBitUnpack (hintBitUnpackContract X86_64.abi) :=
  Verified.of_correct VG.Proof.MlDsa.X86_64.Pack.hintBitUnpack_correct VG.Proof.MlDsa.X86_64.Pack.hintBitUnpack_ct
    { pre := by sig_implies_pre [hintBitUnpackContract, hintBitUnpackSig, VG.Proof.MlDsa.X86_64.Pack.hintBitUnpackK, X86_64.abi, X86_64.argRegs]
      post := by sig_implies_post [hintBitUnpackContract, hintBitUnpackSig, VG.Proof.MlDsa.X86_64.Pack.hintBitUnpackK, X86_64.abi, X86_64.argRegs]
      pub := by sig_implies_pub [hintBitUnpackContract, hintBitUnpackSig, VG.Proof.MlDsa.X86_64.Pack.hintBitUnpackK, X86_64.abi, X86_64.argRegs]
      sat := by
        refine ⟨VG.Proof.MlDsa.X86_64.Pack.hintBitUnpackSat, ?_⟩
        sig_pre [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, X86_64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.X86_64.Pack

end
