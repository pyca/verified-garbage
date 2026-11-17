module

public import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Arm.Leaves
public import VerifiedGarbage.Proof.Dsa.Arm.ValidateOps
import VerifiedGarbage.Proof.Dsa.Frame
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.Arm.Session`, which this module and modules that import it used -/

section

/-!
# DSA on 32-bit ARM: values across operations

The caller's operands (`Input`: a `Ready` operand apart from the whole
working space, with its value) and the computed values in the working space
past the arithmetic (`localVal`) are kept by every operation that does not
store over them (`Input.stage`, `Stage.localVal`), and the flag word by
every operation that stores elsewhere (`Stage.maskW`). A schedule of
operations changes only the working space's arithmetic, its computed values
and the flag word (`Run`): not the saved pointers, nor the saved registers.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm VG.Impl.Dsa.Layout
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)
open VG.Proof.X25519.Arm (Rest)

/-- An operand of the caller, apart from the working space, with value `v`. -/
structure Input (s : State) (base : Addr) (size : Nat) (p : Pointer) (len v : Nat) : Prop
    extends Ready s base p len where
  outside : Region.Disjoint ⟨State.addr (pointerValue base s p), len⟩ ⟨base, size⟩
  value : operand base s p len = v

/-- The working space's memory a schedule may change: the arithmetic's, the
flag word and the computed values. -/
def runRanges : List (Nat × Nat) := [(0, 64), (116, 4), (168, 36), (256, 15456)]

/-- What a schedule keeps. -/
structure Run (base : Addr) (s t : State) : Prop where
  rest : Rest coreClob s t
  mem : Outs base runRanges s.mem t.mem

theorem Run.trans {base : Addr} {s t u : State} (h₁ : Run base s t) (h₂ : Run base t u) : Run base s u :=
  ⟨h₁.rest.trans h₂.rest, h₁.mem.trans h₂.mem⟩

theorem Stage.run {base : Addr} {s t : State} {output len : Nat} (St : Stage base s t output len)
    (ho : output = 116 ∧ len = 4 ∨ 12016 ≤ output ∧ output + len ≤ 15712) : Run base s t :=
  ⟨St.rest, fun x hx => St.mem x fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h₁ := hx (0, 64) (by simp [runRanges])
    have h₂ := hx (116, 4) (by simp [runRanges])
    have h₃ := hx (256, 15456) (by simp [runRanges])
    simp only at h₁ h₂ h₃
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith⟩

theorem Stage.ws {base : Addr} {s t : State} {size output len : Nat} (St : Stage base s t output len)
    (hs : Ws s base size) : Ws t base size :=
  hs.of_rest St.rest (by decide)

theorem Stage.maskW {base : Addr} {s t : State} {output len : Nat} (St : Stage base s t output len)
    (ho : 120 ≤ output) : maskW base t = maskW base s :=
  maskW_keep St.mem fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith

theorem Input.stage {base : Addr} {s t : State} {size output l : Nat} {p : Pointer} {len v : Nat}
    (I : Input s base size p len v) (St : Stage base s t output l) (hout : 116 ≤ output)
    (hz : 12016 ≤ size) (hz2 : size ≤ 2 ^ 32) (ho : output + l ≤ size) : Input t base size p len v := by
  have hO : ∀ r ∈ arithRanges ++ [(output, l)], r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  have hz' : ∀ r ∈ arithRanges ++ [(output, l)], r.1 + r.2 ≤ size := fun r hr => by
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  have P := pointerValue_keep (St.rest.gpr .r12 (by decide)) St.mem hO I.ok
  refine ⟨I.toReady.keep_rest St.rest (O := St.mem) (hO := hO), by rw [P]; exact I.outside, ?_⟩
  rw [operand, P, outs_bytes St.mem (by have := I.fits; omega_using [this]) (fun r hr => by have := hz' r hr; omega_using [hz2, this])
    (fun r hr => I.outside.sub_right (Offset.sub_base base (hz' r hr)))]
  exact I.value

theorem Input.run {base : Addr} {s t : State} {size : Nat} {p : Pointer} {len v : Nat}
    (I : Input s base size p len v) (Rn : Run base s t) (hz : 15712 ≤ size) (hz2 : size ≤ 2 ^ 32) :
    Input t base size p len v := by
  have hO : ∀ r ∈ runRanges, r.1 + r.2 ≤ 64 ∨ 116 ≤ r.1 := by decide
  have hz' : ∀ r ∈ runRanges, r.1 + r.2 ≤ size := fun r hr => by
    simp only [runRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only <;> omega_using [hz]
  have P := pointerValue_keep (Rn.rest.gpr .r12 (by decide)) Rn.mem hO I.ok
  refine ⟨I.toReady.keep_rest Rn.rest (O := Rn.mem) (hO := hO), by rw [P]; exact I.outside, ?_⟩
  rw [operand, P, outs_bytes Rn.mem (by have := I.fits; omega_using [this]) (fun r hr => by have := hz' r hr; omega_using [hz2, this])
    (fun r hr => I.outside.sub_right (Offset.sub_base base (hz' r hr)))]
  exact I.value

theorem Run.ws {base : Addr} {s t : State} {size : Nat} (Rn : Run base s t) (hs : Ws s base size) :
    Ws t base size :=
  hs.of_rest Rn.rest (by decide)

/-! ## Computed values -/

/-- The value of the `len` bytes at offset `o`. -/
abbrev localVal (base : Addr) (s : State) (o len : Nat) : Nat :=
  Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base o) len)

theorem local_addr {s : State} {base : Addr} {size o : Nat} (hs : Ws s base size) (ho : o < size) :
    State.addr (pointerValue base s (.local o)) = off base o := by
  have := hs.ea (r := .r12) (K := 0) (d := o) (BitVec.add_zero _).symm (by omega_using [ho])
  rwa [Nat.zero_add] at this

theorem local_operand {s : State} {base : Addr} {size o len : Nat} (hs : Ws s base size) (ho : o < size) :
    operand base s (.local o) len = localVal base s o len := by
  rw [operand, local_addr hs ho]

theorem localReady {s : State} {base : Addr} {size o len : Nat} (hs : Ws s base size) (ho : 12016 ≤ o)
    (hol : o + len < size) (h16 : o < 2 ^ 16) : Ready s base (.local o) len := by
  have nw := hs.nowrap
  have A := local_addr hs (o := o) (by omega_using [hol])
  refine ⟨h16, ?_, ?_, ?_⟩
  · rw [pointerValue, BitVec.toNat_add, BitVec.toNat_ofNat, hs.wb_toNat, Nat.mod_eq_of_lt (by omega_using [h16] : o < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hol, nw])]
    omega_using [hol, nw]
  · intro e k hek
    rw [A, off, Offset.add_add]
    exact hs.read (by omega_using [hol, hek])
  · rw [A]
    exact Offset.disjoint_base base ho (by omega_using [hol, nw])

theorem Stage.localVal_eq {base : Addr} {s t : State} {output l o len : Nat} (St : Stage base s t output l)
    (ho : 12016 ≤ o) (hb : o + len ≤ 2 ^ 32) (hol : output + l ≤ 2 ^ 32)
    (hsep : o + len ≤ output ∨ output + l ≤ o) : localVal base t o len = localVal base s o len := by
  rw [Arm.localVal, Arm.localVal, outs_bytes St.mem (by omega_using [hb])]
  · intro r hr
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  · intro r hr
    simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint base (.inr (by omega_using [ho])) (by omega_using [hb]) (by omega_using [])
    · exact Offset.disjoint base (.inr (by omega_using [ho])) (by omega_using [hb]) (by omega_using [])
    · exact Offset.disjoint base hsep (by omega_using [hb]) (by omega)

/-- A stored result's value. -/
theorem localVal_of_bytes {base : Addr} {s : State} {o len v : Nat}
    (h : Spec.Rsa.bytesAt s.mem (off base o) len = Spec.Dsa.encodeBE len v) (hv : v < 256 ^ len) :
    localVal base s o len = v := by
  rw [localVal, h, decodeBE_encodeBE hv]

/-- The computed values in `[lo, hi)` are kept. -/
def KeepsLocals (base : Addr) (s t : State) (lo hi : Nat) : Prop :=
  ∀ o len, lo ≤ o → o + len ≤ hi → localVal base t o len = localVal base s o len

theorem KeepsLocals.trans {base : Addr} {s t u : State} {lo hi : Nat} (h₁ : KeepsLocals base s t lo hi)
    (h₂ : KeepsLocals base t u lo hi) : KeepsLocals base s u lo hi :=
  fun o len h h' => (h₂ o len h h').trans (h₁ o len h h')

theorem Stage.keeps {base : Addr} {s t : State} {output l lo hi : Nat} (St : Stage base s t output l)
    (hlo : 12016 ≤ lo) (hhi : hi ≤ 2 ^ 32) (hol : output + l ≤ 2 ^ 32) (hsep : hi ≤ output ∨ output + l ≤ lo) :
    KeepsLocals base s t lo hi :=
  fun _ _ h h' => St.localVal_eq (by omega_using [hlo, h]) (by omega_using [hhi, h']) hol (by omega_using [hsep, h, h'])

end VG.Proof.Dsa.Arm

end

end

/-!
# DSA on 32-bit ARM: the checks of the domain and the keys

`domain_ok`: the flag `&=` the ranges of g and y and `q ∣ p - 1`, and
`q - 2` is stored for the inverses; `subgroup_ok`: `g^q = y^q = 1 mod p`;
`privateKey_ok`: the ranges of x and the nonce, and `g^x = y mod p`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.Ecdsa.Arm (mask32 mask32_and)

variable {umaal : Bool}

/-- Validation leaves the shared helper's register-save words untouched. -/
structure ValidationRun (base : Addr) (s t : State) : Prop extends Run base s t where
  saved : ∀ d, 168 ≤ d → d + 4 ≤ 204 →
    t.mem.readW (off base d) 32 = s.mem.readW (off base d) 32

instance {base s t} : Coe (ValidationRun base s t) (Run base s t) := ⟨ValidationRun.toRun⟩

theorem ValidationRun.trans {base : Addr} {s t u : State}
    (A : ValidationRun base s t) (B : ValidationRun base t u) : ValidationRun base s u :=
  ⟨A.toRun.trans B.toRun, fun d lo hi => (B.saved d lo hi).trans (A.saved d lo hi)⟩

theorem Stage.validationRun {base : Addr} {s t : State} {o l : Nat}
    (St : Stage base s t o l) (H : o = 116 ∧ l = 4 ∨ 12016 ≤ o ∧ o + l ≤ 15712) :
    ValidationRun base s t := by
  refine ⟨St.run H, fun d lo hi => Mem.readW_congr fun i hᵢ => ?_⟩
  apply St.mem
  intro r hr
  simp only [arithRanges, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [ofs_off base (by omega_arith)]
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith

/-- The working space and the widths of a call. -/
structure Sched (s : State) (base : Addr) (size pLen qLen nP nQ : Nat) : Prop where
  ws : Ws s base size
  big : 15712 < size
  wp : Width pLen nP
  wq : Width qLen nQ
  qp : qLen ≤ pLen
  q32 : qLen ≤ 32

theorem Sched.run {s t : State} {base : Addr} {size pLen qLen nP nQ : Nat} (S : Sched s base size pLen qLen nP nQ)
    (Rn : Run base s t) : Sched t base size pLen qLen nP nQ :=
  ⟨Rn.ws S.ws, S.big, S.wp, S.wq, S.qp, S.q32⟩

theorem Sched.stage {s t : State} {base : Addr} {size pLen qLen nP nQ o l : Nat}
    (S : Sched s base size pLen qLen nP nQ) (St : Stage base s t o l) : Sched t base size pLen qLen nP nQ :=
  ⟨St.ws S.ws, S.big, S.wp, S.wq, S.qp, S.q32⟩

theorem Sched.fits {s : State} {base : Addr} {size pLen qLen nP nQ : Nat} (S : Sched s base size pLen qLen nP nQ) :
    size ≤ 2 ^ 32 := by
  have := S.ws.nowrap; omega_using [this]

theorem Sched.lens {s : State} {base : Addr} {size pLen qLen nP nQ : Nat} (S : Sched s base size pLen qLen nP nQ) :
    4 ≤ qLen ∧ qLen ≤ pLen ∧ pLen ≤ 384 ∧ qLen ≤ 32 ∧ pLen % 4 = 0 ∧ qLen % 4 = 0 :=
  ⟨S.wq.four, S.qp, S.wp.max, S.q32, S.wp.word, S.wq.word⟩

/-- An input after an operation that writes the flag or a computed value. -/
theorem Input.next {s t : State} {base : Addr} {size pLen qLen nP nQ o l : Nat} {p : Impl.Dsa.Layout.Pointer}
    {len v : Nat} (I : Input s base size p len v) (S : Sched s base size pLen qLen nP nQ) (St : Stage base s t o l)
    (ho : o = 116 ∧ l = 4 ∨ 12016 ≤ o ∧ o + l ≤ 15712) : Input t base size p len v :=
  I.stage St (by omega_using [ho]) (by have := S.big; omega_using [this]) S.fits (by have := S.big; omega_using [ho, this])

theorem operand_lt_of {base : Addr} {s : State} {size : Nat} {p : Impl.Dsa.Layout.Pointer} {len v : Nat}
    (I : Input s base size p len v) : v < 256 ^ len :=
  I.value ▸ operand_lt base s p len

theorem domain_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Validate.domain pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (((1 < G ∧ G < P) ∧ (1 < Y ∧ Y < P)) ∧ (P - 1) % Q = 0) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ ValidationRun base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  obtain Plt := operand_lt_of Ip
  obtain Qlt := operand_lt_of Iq
  simp only [Validate.domain, Core.sequence, List.foldr]
  refine WP.seq (WP.seq (WP.mono (range_ok S.ws (by omega_using [big]) S.wp Ip.toReady Ig.toReady true) fun v₁ ⟨F₁, St₁⟩ =>
    WP.mono (range_ok (St₁.ws S.ws) (by omega_using [big]) S.wp (Ip.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady
      (Iy.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady true) fun v₂ ⟨F₂, St₂⟩ => ?_))
  obtain S₂ := (S.stage St₁).stage St₂
  obtain Ip₂ := (Ip.next S St₁ (.inl ⟨rfl, rfl⟩)).next (S.stage St₁) St₂ (.inl ⟨rfl, rfl⟩)
  obtain Iq₂ := (Iq.next S St₁ (.inl ⟨rfl, rfl⟩)).next (S.stage St₁) St₂ (.inl ⟨rfl, rfl⟩)
  rw [(Ip.next S St₁ (.inl ⟨rfl, rfl⟩)).value, (Iy.next S St₁ (.inl ⟨rfl, rfl⟩)).value] at F₂
  rw [Ip.value, Ig.value] at F₁
  -- `p - 1`
  refine WP.seq (WP.mono (minus_ok (output := Impl.Dsa.Layout.t) S₂.ws (by omega_using [big]) S.wp Ip₂.toReady Ip₂.value hP hPo
    (by omega_using [hP]) (by decide) (by decide) (by simp only [Impl.Dsa.Layout.t]; omega_using [p384, big]) (by decide))
    fun v₃ ⟨B₃, St₃⟩ => ?_)
  obtain S₃ := S₂.stage St₃
  obtain ho₃ : 12016 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega_using [p384]
  obtain Iq₃ := Iq₂.next S₂ St₃ (.inr ho₃)
  obtain L₃ : localVal base v₃ Impl.Dsa.Layout.t pLen = P - 1 := localVal_of_bytes B₃ (by omega_using [Plt])
  -- `(p - 1) mod q`
  refine WP.seq (WP.mono (reduce_ok (output := Impl.Dsa.Layout.u) S₃.ws (by omega_using [big]) S.wq Iq₃.toReady
    (count := .imm pLen) (input := .local Impl.Dsa.Layout.t) (show pLen < 2 ^ 16 by omega_using [p384])
    (localReady S₃.ws (by decide) (by simp only [countValue, Impl.Dsa.Layout.t]; omega_using [p384, big]) (by decide))
    Iq₃.value hQ hQo (by decide) (by simp only [Impl.Dsa.Layout.u]; omega_using [q32, big]) (by decide)) fun v₄ ⟨B₄, St₄⟩ => ?_)
  rw [countValue, local_operand S₃.ws (by simp only [Impl.Dsa.Layout.t]; omega_using [big]), L₃] at B₄
  obtain S₄ := S₃.stage St₄
  obtain ho₄ : 12016 ≤ Impl.Dsa.Layout.u ∧ Impl.Dsa.Layout.u + qLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.u]; omega_using [q32]
  obtain Iq₄ := Iq₃.next S₃ St₄ (.inr ho₄)
  obtain L₄ : localVal base v₄ Impl.Dsa.Layout.u qLen = (P - 1) % Q :=
    localVal_of_bytes B₄ (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_using [hQ])) (Nat.le_of_lt Qlt))
  -- `q ∣ p - 1`
  refine WP.seq (WP.mono (zero_ok S₄.ws (by omega_using [big]) S.wq
    (localReady (len := qLen) S₄.ws (by decide) (by simp only [Impl.Dsa.Layout.u]; omega_using [q32, big]) (by decide)) false)
    fun v₅ ⟨F₅, St₅⟩ => ?_)
  rw [local_operand S₄.ws (by simp only [Impl.Dsa.Layout.u]; omega_using [big]), L₄] at F₅
  obtain S₅ := S₄.stage St₅
  obtain Iq₅ := Iq₄.next S₄ St₅ (.inl ⟨rfl, rfl⟩)
  -- `q - 2`
  refine WP.seq (WP.mono (minus_ok (output := Impl.Dsa.Layout.qMinusTwo) S₅.ws (by omega_using [big]) S.wq Iq₅.toReady
    Iq₅.value (by omega_using [hQ]) hQo (by omega_using [hQ]) (by decide) (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo]; omega_using [q32, big])
    (by decide)) fun v₆ ⟨B₆, St₆⟩ => WP.block_nil ⟨?_, localVal_of_bytes B₆ (by omega_using [Qlt]), ?_⟩)
  · rw [St₆.maskW (by decide), F₅, St₄.maskW (by decide), St₃.maskW (by decide), F₂, F₁,
      BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [↓reduceIte, Bool.false_eq_true]; omega_using []))
  · exact ((((St₁.validationRun (.inl ⟨rfl, rfl⟩)).trans (St₂.validationRun (.inl ⟨rfl, rfl⟩))).trans (St₃.validationRun (.inr ho₃))).trans
      ((St₄.validationRun (.inr ho₄)).trans (St₅.validationRun (.inl ⟨rfl, rfl⟩)))).trans
      (St₆.validationRun (.inr (by simp only [Impl.Dsa.Layout.qMinusTwo]; omega_using [q32])))

/-- The window of the scalars below `t`. -/
abbrev scalars : Nat × Nat := (12016, Impl.Dsa.Layout.t)

theorem subgroup_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) :
    WP isa (Validate.subgroup umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (G ^ Q % P = 1 ∧ Y ^ Q % P = 1) ∧
      KeepsLocals base s t scalars.1 scalars.2 ∧ ValidationRun base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  obtain Plt := operand_lt_of Ip
  obtain ho : 12016 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega_using [p384]
  obtain ht : Impl.Dsa.Layout.t + pLen < size := by omega_using [big, ho]
  simp only [Validate.subgroup, Core.sequence, List.foldr]
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S.ws (by omega_using [big]) S.wp q4 qp qw Ip.toReady
    Ig.toReady Iq.toReady Ip.value hP hPo ho.1 (by omega_using [big, ho]) (by decide)) fun v₁ ⟨B₁, St₁⟩ => ?_)
  rw [Ig.value, Iq.value] at B₁
  obtain S₁ := S.stage St₁
  refine WP.seq (WP.mono (isOne_ok S₁.ws (by omega_using [big]) S.wp (localReady S₁.ws ho.1 ht (by decide)))
    fun v₂ ⟨F₂, St₂⟩ => ?_)
  rw [local_operand S₁.ws (by omega_using [big, ho]), localVal_of_bytes B₁ (Nat.lt_trans (Nat.mod_lt _ (by omega_using [hP])) Plt)] at F₂
  obtain S₂ := S₁.stage St₂
  obtain Ip₂ := (Ip.next S St₁ (.inr ho)).next S₁ St₂ (.inl ⟨rfl, rfl⟩)
  obtain Iq₂ := (Iq.next S St₁ (.inr ho)).next S₁ St₂ (.inl ⟨rfl, rfl⟩)
  obtain Iy₂ := (Iy.next S St₁ (.inr ho)).next S₁ St₂ (.inl ⟨rfl, rfl⟩)
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S₂.ws (by omega_using [big]) S.wp q4 qp qw Ip₂.toReady
    Iy₂.toReady Iq₂.toReady Ip₂.value hP hPo ho.1 (by omega_using [big, ho]) (by decide)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [Iy₂.value, Iq₂.value] at B₃
  obtain S₃ := S₂.stage St₃
  refine WP.seq (WP.mono (isOne_ok S₃.ws (by omega_using [big]) S.wp (localReady S₃.ws ho.1 ht (by decide)))
    fun v₄ ⟨F₄, St₄⟩ => WP.block_nil ⟨?_, ?_, ?_⟩)
  · rw [local_operand S₃.ws (by omega_using [big, ho]), localVal_of_bytes B₃ (Nat.lt_trans (Nat.mod_lt _ (by omega_using [hP])) Plt)] at F₄
    rw [F₄, St₃.maskW (by decide), F₂, St₁.maskW (by decide), BitVec.and_assoc, mask32_and]
  · have k : ∀ {a b : State} {o l : Nat}, Stage base a b o l → o + l ≤ 15712 →
        (14944 ≤ o ∨ o + l ≤ 12016) → KeepsLocals base a b scalars.1 scalars.2 := fun St h₁ h₂ =>
      St.keeps (by decide) (by decide) (by omega_using [h₁]) (by simp only [Impl.Dsa.Layout.t]; omega_using [h₂])
    have ht' : Impl.Dsa.Layout.t = 14944 := rfl
    exact (((k St₁ (by omega_using [ho]) (by omega_using [ht'])).trans (k St₂ (by decide) (by decide))).trans
      (k St₃ (by omega_using [ho]) (by omega_using [ht']))).trans (k St₄ (by decide) (by decide))
  · exact (((St₁.validationRun (.inr ho)).trans (St₂.validationRun (.inl ⟨rfl, rfl⟩))).trans (St₃.validationRun (.inr ho))).trans
      (St₄.validationRun (.inl ⟨rfl, rfl⟩))

theorem Stage.keepsScalars {base : Addr} {a b : State} {o l : Nat} (St : Stage base a b o l) (h₁ : o + l ≤ 15712)
    (h₂ : 14944 ≤ o ∨ o + l ≤ 12016) : KeepsLocals base a b scalars.1 scalars.2 :=
  St.keeps (by decide) (by decide) (by omega_using [h₁]) (by simp only [Impl.Dsa.Layout.t]; omega_using [h₂])

theorem publicKey_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (hP : 1 < P) (hPo : P % 2 = 1) (hQ : 255 < Q) (hQo : Q % 2 = 1) :
    WP isa (Validate.publicKey umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (publicChecks P Q G Y) ∧
      localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 ∧ ValidationRun base s t := by
  have big := S.big
  have fits := S.fits
  unfold Validate.publicKey
  refine WP.seq (WP.mono (domain_ok S Ip Iq Ig Iy hP hPo hQ hQo) fun u ⟨Fu, Lu, Ru⟩ =>
    WP.mono (subgroup_ok (S.run Ru) (Ip.run Ru (by omega_using [big]) fits) (Iq.run Ru (by omega_using [big]) fits)
      (Ig.run Ru (by omega_using [big]) fits) (Iy.run Ru (by omega_using [big]) fits) hP hPo) fun t ⟨Ft, Kt, Rt⟩ => ?_)
  obtain L : localVal base t Impl.Dsa.Layout.qMinusTwo qLen = Q - 2 := by
    rw [Kt _ _ (by decide) (by simp only [Impl.Dsa.Layout.qMinusTwo, Impl.Dsa.Layout.t]; have := S.q32; omega_using [this])]
    exact Lu
  refine ⟨?_, L, Ru.trans Rt⟩
  rw [Ft, Fu, BitVec.and_assoc, mask32_and]
  exact congrArg _ (mask32_iff (by simp only [publicChecks, and_assoc]))

theorem privateKey_ok {s : State} {base : Addr} {size pLen qLen nP nQ P Q G Y X K : Nat}
    (S : Sched s base size pLen qLen nP nQ)
    (Ip : Input s base size (.input .p) pLen P) (Iq : Input s base size (.input .q) qLen Q)
    (Ig : Input s base size (.input .g) pLen G) (Iy : Input s base size (.input .y) pLen Y)
    (Ix : Input s base size (.input .x) qLen X) (Ik : Input s base size (.input .nonce) qLen K)
    (hP : 1 < P) (hPo : P % 2 = 1) :
    WP isa (Validate.privateKey umaal pLen qLen) s fun t =>
      maskW base t = maskW base s &&& mask32 (((0 < X ∧ X < Q) ∧ (0 < K ∧ K < Q)) ∧ G ^ X % P = Y) ∧
      KeepsLocals base s t scalars.1 scalars.2 ∧ Run base s t := by
  obtain ⟨q4, qp, p384, q32, pw, qw⟩ := S.lens
  have big := S.big
  have fits := S.fits
  obtain Plt := operand_lt_of Ip
  obtain ho : 12016 ≤ Impl.Dsa.Layout.t ∧ Impl.Dsa.Layout.t + pLen ≤ 15712 := by
    simp only [Impl.Dsa.Layout.t]; omega_using [p384]
  obtain ht : Impl.Dsa.Layout.t + pLen < size := by omega_using [big, ho]
  have ht' : Impl.Dsa.Layout.t = 14944 := rfl
  simp only [Validate.privateKey, Core.sequence, List.foldr]
  refine WP.seq (WP.seq (WP.mono (range_ok S.ws (by omega_using [big]) S.wq Iq.toReady Ix.toReady false) fun v₁ ⟨F₁, St₁⟩ =>
    WP.mono (range_ok (St₁.ws S.ws) (by omega_using [big]) S.wq (Iq.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady
      (Ik.next S St₁ (.inl ⟨rfl, rfl⟩)).toReady false) fun v₂ ⟨F₂, St₂⟩ => ?_))
  rw [Iq.value, Ix.value] at F₁
  rw [(Iq.next S St₁ (.inl ⟨rfl, rfl⟩)).value, (Ik.next S St₁ (.inl ⟨rfl, rfl⟩)).value] at F₂
  obtain S₂ := (S.stage St₁).stage St₂
  obtain nx : ∀ {p : Impl.Dsa.Layout.Pointer} {len v : Nat}, Input s base size p len v → Input v₂ base size p len v :=
    fun I => (I.next S St₁ (.inl ⟨rfl, rfl⟩)).next (S.stage St₁) St₂ (.inl ⟨rfl, rfl⟩)
  refine WP.seq (WP.mono (power_ok (output := Impl.Dsa.Layout.t) S₂.ws (by omega_using [big]) S.wp q4 qp qw (nx Ip).toReady
    (nx Ig).toReady (nx Ix).toReady (nx Ip).value hP hPo ho.1 (by omega_using [big, ho]) (by decide)) fun v₃ ⟨B₃, St₃⟩ => ?_)
  rw [(nx Ig).value, (nx Ix).value] at B₃
  obtain S₃ := S₂.stage St₃
  obtain Iy₃ := (nx Iy).next S₂ St₃ (.inr ho)
  refine WP.seq (WP.mono (equalValues_ok S₃.ws (by omega_using [big]) S.wp (localReady S₃.ws ho.1 ht (by decide)) Iy₃.toReady)
    fun v₄ ⟨F₄, St₄⟩ => WP.block_nil ⟨?_, ?_, ?_⟩)
  · rw [local_operand S₃.ws (by omega_using [big, ho]), localVal_of_bytes B₃ (Nat.lt_trans (Nat.mod_lt _ (by omega_using [hP])) Plt),
      Iy₃.value] at F₄
    rw [F₄, St₃.maskW (by decide), F₂, F₁, BitVec.and_assoc, BitVec.and_assoc, mask32_and, mask32_and]
    exact congrArg _ (mask32_iff (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using []))
  · exact (((St₁.keepsScalars (by decide) (by decide)).trans (St₂.keepsScalars (by decide) (by decide))).trans
      (St₃.keepsScalars (by omega_using [ho]) (by omega_using [ht']))).trans (St₄.keepsScalars (by decide) (by decide))
  · exact (((St₁.run (.inl ⟨rfl, rfl⟩)).trans (St₂.run (.inl ⟨rfl, rfl⟩))).trans (St₃.run (.inr ho))).trans
      (St₄.run (.inl ⟨rfl, rfl⟩))

end VG.Proof.Dsa.Arm
