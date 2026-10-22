module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecAl
import VerifiedGarbage.Proof.RsaPkcs1Sig.BytesAt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecTaint

/-!
# RSAES-PKCS1-v1_5 decryption on x86: the scan of `EM`

As on ARMv7 (`Proof/RsaPkcs1Enc/Arm/DecScan.lean`): what `out` holds after
the private-key operation (`emOf`: `EM`, or zeros for an error) and the
call's result (`rcOf`). The scan of `EM` from index 2 for its first zero
(`scanLoop_vp`): whether there is one, as a mask (`mk`), and where
(`Proof.RsaPkcs1Enc.firstZero`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.X86.Dec

open VG VG.Impl.RsaPkcs1Enc.X86.Decrypt VG.Proof.RsaPkcs1Sig.X86
open VG.X86 hiding frameBytes
open VG.X86.Wp
open VG.Proof.Pbkdf2.Stream.X86 (wp_xori)
open VG.Proof.RsaPkcs1Enc (firstZero)

variable {P : EP}

/-! ## `out` and the result after the call -/

/-- `out` after the call: `EM`, or zeros. -/
def emOf (P : EP) (σ : State) : List Byte :=
  match privO P σ with
  | .ok y => y
  | _ => List.replicate P.K 0

/-- The call's result. -/
def rcOf (P : EP) (σ : State) : BitVec 32 :=
  match privO P σ with
  | .ok _ => 1
  | .invalid => 0
  | .fault => 2

theorem Priv.em {σ : State} {m : Mem} {rc : BitVec 32} (h : Priv P σ m rc) :
    Spec.Rsa.bytesAt m (P.out.setWidth 64) P.K = emOf P σ ∧ rc = rcOf P σ := by
  unfold Priv at h
  unfold emOf rcOf
  generalize privO P σ = o at h ⊢
  cases o <;> exact ⟨h.2, h.1⟩

theorem rcOf_cases (P : EP) (σ : State) : rcOf P σ = 1 ∨ rcOf P σ = 0 ∨ rcOf P σ = 2 := by
  unfold rcOf; split <;> simp

/-- `out`, the result in its slot, and `AL` in its slot. -/
def SB (P : EP) (σ s : State) : Prop :=
  AL P σ s ∧ Spec.Rsa.bytesAt s.mem (P.out.setWidth 64) P.K = emOf P σ ∧
    s.mem.readW (P.lay.fr oR) 32 = rcOf P σ

theorem AL.sb {σ s : State} (h : AL P σ s) : SB P σ s := by
  obtain ⟨rc, pr, sl⟩ := h.1.1.2
  have e := Priv.em pr
  exact ⟨h, e.1, by rw [sl, e.2]⟩

theorem emOf_length {σ s : State} (h : SB P σ s) : (emOf P σ).length = P.K := by
  rw [← h.2.1, Proof.RsaPkcs1Sig.bytesAt_len]

theorem SB.of_mem {σ s t : State} (h : SB P σ s) (st : P.lay.St σ t) (hm : t.mem = s.mem) : SB P σ t :=
  ⟨⟨h.1.1.of_mem st hm, by rw [hm]; exact h.1.2⟩, by rw [hm]; exact h.2.1, by rw [hm]; exact h.2.2⟩

theorem SB.S {σ s : State} (h : SB P σ s) : S P σ s := h.1.1.1.1

/-! ## Addresses in `out` -/

namespace In
variable {σ : State} (h : In P σ)
include h

theorem out_fit : P.out.toNat + P.K ≤ 2 ^ 32 := by
  have := h.ok.fits P.OUT (by simp)
  simp only [BitVec.toNat_setWidth] at this
  rwa [Nat.mod_eq_of_lt (by have := P.out.isLt; omega)] at this

theorem outA {i d : Nat} (hi : i + d < P.K) : addr (P.out + BitVec.ofNat 32 i) d = P.out.setWidth 64 + BitVec.ofNat 64 (i + d) := by
  have := h.out_fit
  rw [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact addr_eq (by omega)

end In

theorem St.out_w {σ s : State} (hs : S P σ s) {i n : Nat} (hn : i + n ≤ P.K) :
    InRegions s.wr (P.out.setWidth 64 + BitVec.ofNat 64 i) n :=
  ⟨P.OUT, hs.2.inRw (by simp), Offset.contains_base _ hn (by have := hs.1.k1024; omega)⟩

theorem St.out_r {σ s : State} (hs : S P σ s) {i n : Nat} (hn : i + n ≤ P.K) :
    InRegions (s.rd ++ s.wr) (P.out.setWidth 64 + BitVec.ofNat 64 i) n :=
  let ⟨r, hr, hc⟩ := St.out_w hs hn
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Byte `i` of `out`. -/
theorem SB.byte {σ s : State} (h : SB P σ s) {i : Nat} (hi : i < P.K) :
    s.mem (P.out.setWidth 64 + BitVec.ofNat 64 i) = (emOf P σ).getD i 1 := by
  rw [← h.2.1, Proof.RsaPkcs1Sig.bytesAt_getD hi]

/-! ## Masks -/

/-- A condition as a mask: all ones or zero. -/
def mk (b : Bool) : BitVec 32 := if b then BitVec.allOnes 32 else 0#32

theorem sbb_mk (c : Bool) : (if c = true then BitVec.allOnes 32 else 0) = mk c := rfl

/-- `b - 1` borrows exactly when the byte `b` is zero. -/
theorem zcf (b : Byte) : decide ((b.setWidth 32).toNat < (1 : BitVec 32).toNat) = decide (b = 0) := by
  have e1 : (1 : BitVec 32).toNat = 1 := rfl
  rw [e1, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega)]
  by_cases h : b = 0
  · subst h; rfl
  · have : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    rw [decide_eq_false h, decide_eq_false (by omega)]

/-! ## The scan -/

/-- The first zero of `EM` before index `i`. -/
abbrev fz (P : EP) (σ : State) (i : Nat) : Option Nat := firstZero (emOf P σ) i

/-- `j` bytes scanned, from index 2. -/
def SCI (P : EP) (j : Nat) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .esi = P.out + BitVec.ofNat 32 (2 + j) ∧ s.gpr .edx = BitVec.ofNat 32 (2 + j) ∧
    s.gpr .ecx = BitVec.ofNat 32 (P.K - 2 - j) ∧ s.gpr .ebx = mk (fz P σ (2 + j)).isSome ∧
    s.gpr .edi = BitVec.ofNat 32 ((fz P σ (2 + j)).getD 0)

theorem firstZero_two (EM : List Byte) : firstZero EM 2 = none := rfl

theorem scanInit_vp : VP (AL P) (.block scanInit) (SCI P 0) :=
  VP.taint [.esp] scanInit_taint (sp_agree fun _ _ h => h.1.1.1) fun σ s h => by
    have hb := h.sb
    have hs := hb.S
    have hK := hs.1.k64
    simp only [scanInit]
    refine St.argv hs (j := 0) (by decide) (d := .esi) (by decide) fun t1 s1 u1 => ?_
    refine wp_addi fun t2 u2 => ?_
    have s2 : S P σ t2 := ⟨hs.1, s1.2.upd u2 (by decide)⟩
    refine St.argv s2 (j := 4) (by decide) (d := .ecx) (by decide) fun t3 s3 u3 => ?_
    refine wp_subi fun t4 u4 _ _ => ?_
    have s4 : S P σ t4 := ⟨hs.1, s3.2.upd u4 (by decide)⟩
    refine St.movi s4 (d := .edx) (by decide) 2 fun t5 s5 u5 => ?_
    refine St.movi s5 (d := .ebx) (by decide) 0 fun t6 s6 u6 => ?_
    refine St.movi s6 (d := .edi) (by decide) 0 fun t7 s7 u7 => WP.block_nil ?_
    have mm : t7.mem = s.mem := by rw [u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
    refine ⟨hb.of_mem s7.2 mm, ?_, ?_, ?_, ?_, ?_⟩
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.other, u3.other, u2.gpr, u1.gpr]; rfl
    · simp (disch := decide) only [u7.other, u6.other, u5.gpr]
    · simp (disch := decide) only [u7.other, u6.other, u5.other, u4.gpr, u3.gpr]
      exact Offset.ofNat_sub_ofNat (d := 2) (by omega)
    · simp (disch := decide) only [u7.other, u6.gpr]; rfl
    · rw [u7.gpr]; rfl

/-- `m` bytes left. -/
def SCM (P : EP) (m : Nat) (σ s : State) : Prop := m ≤ P.K - 2 ∧ SCI P (P.K - 2 - m) σ s

/-- The scan done. -/
def SCQ (P : EP) (σ s : State) : Prop :=
  SB P σ s ∧ s.gpr .ebx = mk (fz P σ P.K).isSome ∧ s.gpr .edi = BitVec.ofNat 32 ((fz P σ P.K).getD 0)

/-- One step of the scan, at index `i`. -/
theorem scan_step (EM : List Byte) {i : Nat} (hi : 2 ≤ i) :
    (BitVec.ofNat 32 ((firstZero EM i).getD 0) |||
      ((mk (firstZero EM i).isSome ^^^ BitVec.allOnes 32) &&& mk (decide (EM.getD i 1 = 0)) &&& BitVec.ofNat 32 i) =
        BitVec.ofNat 32 ((firstZero EM (i + 1)).getD 0)) ∧
    (mk (firstZero EM i).isSome ||| mk (decide (EM.getD i 1 = 0)) = mk (firstZero EM (i + 1)).isSome) := by
  rw [firstZero]
  cases hf : firstZero EM i with
  | some k =>
    simp only [Option.isSome_some, Option.getD_some, mk, ↓reduceIte, BitVec.xor_self, BitVec.zero_and,
      BitVec.or_zero, BitVec.allOnes_or, and_self]
  | none =>
    simp only [Option.isSome_none, Option.getD_none, mk, Bool.false_eq_true, ↓reduceIte, BitVec.zero_xor,
      BitVec.allOnes_and, BitVec.zero_or]
    by_cases e : EM.getD i 1 = 0
    · simp only [e, decide_true, ↓reduceIte, hi, and_self, Option.getD_some, Option.isSome_some,
        BitVec.allOnes_and]
    · simp only [e, decide_false, Bool.false_eq_true, ↓reduceIte, and_false, Option.getD_none,
        Option.isSome_none, BitVec.zero_and]
      constructor <;> first | trivial | rfl

theorem ofNat_beq_zero' {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n == 0) = decide (n = 0) :=
  ofNat_beq_zero hn

theorem scanBody_vp (n : Nat) : VP (SCM P (n + 1)) (.block scanBody) fun σ s =>
    isa.eval .ne s = some (decide (0 < n)) ∧ (n = 0 → SCQ P σ s) ∧ (0 < n → SCM P n σ s) := by
  refine VP.taint [.esi, .ecx] scanBody_taint (fun _ _ _ _ h₁ h₂ r hr => ?_) fun σ s h => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.2.2.1, h₂.2.2.1]
    · rw [h₁.2.2.2.2.1, h₂.2.2.2.2.1]
  obtain ⟨hn, hb, si, dx, cx, bx, di⟩ := h
  generalize hj : P.K - 2 - (n + 1) = j at si dx cx bx di
  have hs := hb.S
  have hK := hs.1.k64
  have hK' := hs.1.k1024
  have hjK : 2 + j < P.K := by omega
  simp only [scanBody]
  refine wp_movzx8 (a := P.out.setWidth 64 + BitVec.ofNat 64 (2 + j))
    (by show s.ea ⟨.esi, 0⟩ = _; rw [ea_at, si, hs.1.outA (d := 0) (by omega)]; rfl) (St.out_r hs (by omega)) fun t1 u1 => ?_
  refine wp_subi fun t2 u2 c2 _ => ?_
  refine wp_sbb_self c2 fun t3 u3 => ?_
  refine wp_mov fun t4 u4 => ?_
  refine wp_xori fun t5 u5 => ?_
  refine wp_and fun t6 u6 => ?_
  refine wp_and fun t7 u7 => ?_
  refine wp_or fun t8 u8 => ?_
  refine wp_or fun t9 u9 => ?_
  refine wp_addi fun t10 u10 => ?_
  refine wp_addi fun t11 u11 => ?_
  refine wp_subi fun t12 u12 _ hz => WP.block_nil ?_
  have mm : t12.mem = s.mem := by
    rw [u12.mem, u11.mem, u10.mem, u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem]
  have st : P.lay.St σ t12 := hs.2.regs (by rw [u12.rd, u11.rd, u10.rd, u9.rd, u8.rd, u7.rd, u6.rd, u5.rd,
      u4.rd, u3.rd, u2.rd, u1.rd])
    (by rw [u12.wr, u11.wr, u10.wr, u9.wr, u8.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr])
    (by simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]) mm
  have z3 : t3.gpr .eax = mk (decide ((emOf P σ).getD (2 + j) 1 = 0)) := by
    rw [u3.gpr, sbb_mk, u1.gpr, hb.byte hjK, zcf]
  have step := scan_step (emOf P σ) (i := 2 + j) (by omega)
  have bp7 : t7.gpr .ebp = (mk (fz P σ (2 + j)).isSome ^^^ BitVec.allOnes 32) &&&
      mk (decide ((emOf P σ).getD (2 + j) 1 = 0)) &&& BitVec.ofNat 32 (2 + j) := by
    rw [u7.gpr, u6.gpr, u5.gpr, u4.gpr]
    simp (disch := decide) only [u6.other, u5.other, u4.other]
    rw [z3]
    simp (disch := decide) only [u3.other, u2.other, u1.other]
    rw [bx, dx]
  have dit : t12.gpr .edi = BitVec.ofNat 32 ((fz P σ (2 + j + 1)).getD 0) := by
    simp (disch := decide) only [u12.other, u11.other, u10.other, u9.other]
    rw [u8.gpr, bp7, u7.other _ (by decide)]
    simp (disch := decide) only [u6.other, u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [di]; exact step.1
  have bxt : t12.gpr .ebx = mk (fz P σ (2 + j + 1)).isSome := by
    simp (disch := decide) only [u12.other, u11.other, u10.other]
    rw [u9.gpr]
    simp (disch := decide) only [u8.other, u7.other, u6.other, u5.other, u4.other]
    rw [z3]
    simp (disch := decide) only [u3.other, u2.other, u1.other]
    rw [bx]; exact step.2
  have dxt : t12.gpr .edx = BitVec.ofNat 32 (2 + j + 1) := by
    simp (disch := decide) only [u12.other, u11.other, u10.gpr, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [dx]; exact Proof.Pbkdf2.Stream.X86.ofNat_succ32 _
  have sit : t12.gpr .esi = P.out + BitVec.ofNat 32 (2 + j + 1) := by
    simp (disch := decide) only [u12.other, u11.gpr, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [si, BitVec.add_assoc]; exact congrArg (P.out + ·) (Proof.Pbkdf2.Stream.X86.ofNat_succ32 _)
  have cx11 : t11.gpr .ecx = BitVec.ofNat 32 (n + 1) := by
    simp (disch := decide) only [u11.other, u10.other, u9.other, u8.other, u7.other, u6.other,
      u5.other, u4.other, u3.other, u2.other, u1.other]
    rw [cx, show P.K - 2 - j = n + 1 by omega]
  have cxt : t12.gpr .ecx = BitVec.ofNat 32 n := by
    rw [u12.gpr, cx11]; exact Offset.ofNat_sub_ofNat (d := 1) (by omega)
  have sb := hb.of_mem st mm
  refine ⟨?_, fun h0 => ⟨sb, ?_, ?_⟩, fun h0 => ⟨by omega, sb, ?_, ?_, ?_, ?_, ?_⟩⟩
  · show eval .ne t12 = _
    rw [cx11, show BitVec.ofNat 32 (n + 1) - 1 = BitVec.ofNat 32 n from
      Offset.ofNat_sub_ofNat (d := 1) (by omega), ofNat_beq_zero (by omega)] at hz
    simp only [eval, hz]
    by_cases h0 : n = 0 <;> simp [h0] <;> omega
  · rw [bxt, show 2 + j + 1 = P.K by omega]
  · rw [dit, show 2 + j + 1 = P.K by omega]
  · rw [sit, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega]
  · rw [dxt, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega]
  · rw [cxt, show P.K - 2 - (P.K - 2 - n) = n by omega]
  · rw [bxt, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega]
  · rw [dit, show 2 + (P.K - 2 - n) = 2 + j + 1 by omega]

theorem scanLoop_vp : VP (SCI P 0) scanLoop (SCQ P) := by
  refine (VP.loop (I := SCM P) scanBody_vp (P.K - 2 - 1)).mono (fun σ s h => ?_) fun _ _ h => h
  have hK := h.1.S.1.k64
  exact ⟨by omega, by rw [show P.K - 2 - (P.K - 2 - 1 + 1) = 0 by omega]; exact h⟩

end VG.Proof.RsaPkcs1Enc.X86.Dec
