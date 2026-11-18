module

public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Reduce
public import VerifiedGarbage.Impl.Bignum.Arm.Fios2
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

/-! ### `Bignum.Arm.Fios2.Args`, which the modules that import this one used -/

section

/-! Enter a two-row round: both words of the first operand, the pointers,
the inverse in both quotient registers, and four clear carries. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_mov op2_imm op2_reg)

theorem args_ok (s : State) {base : BitVec 32} {size tmp a b mod acc n i : Nat} {inv : BitVec 32}
    (ctx : RoundCtx s base size tmp a b mod acc n)
    (hdr : RoundMeta s.mem base tmp a b mod acc n i inv) (hi : i + 2 ≤ n)
    (ptr : s.gpr .r0 = base + BitVec.ofNat 32 tmp) :
    WP isa (.block VG.Impl.Bignum.Arm.Fios2.args) s fun t =>
      t.gpr .r1 = s.mem.readW (off (State.addr base) (a + 4 * i)) 32 ∧
      t.gpr .r9 = s.mem.readW (off (State.addr base) (a + 4 * i + 4)) 32 ∧
      t.gpr .r0 = base + BitVec.ofNat 32 acc ∧ t.gpr .r12 = base + BitVec.ofNat 32 b ∧
      t.gpr .r4 = base + BitVec.ofNat 32 mod ∧ t.gpr .r2 = inv ∧ t.gpr .r10 = inv ∧
      t.gpr .lr = BitVec.ofNat 32 n ∧ t.gpr .r7 = 0 ∧ t.gpr .r8 = 0 ∧ t.gpr .r5 = 0 ∧
      t.gpr .r11 = 0 ∧ t.mem = s.mem ∧ Rest roundClobbers s t := by
  have ws := ctx.workspace
  have ht := ctx.tmpFits
  have ha := ctx.aFits
  unfold VG.Impl.Bignum.Arm.Fios2.args
  refine wp_ldr (by decide) (ws.ea ptr (by omega_using [ht])) (ws.read (by omega_using [ht])) fun s1 u1 => ?_
  obtain w1 := ws.congr u1.wr
  obtain a1 : s1.gpr .r3 = base + BitVec.ofNat 32 (a + 4 * i) := u1.gpr.trans hdr.aPtr
  refine wp_ldr (a := off (State.addr base) (a + 4 * i)) (by decide)
    (by simpa only [Nat.add_zero] using w1.ea a1 (imm := 0) (by omega_using [hi, ha])) (w1.read (by omega_using [hi, ha])) fun s2 u2 => ?_
  refine wp_ldr (a := off (State.addr base) (a + 4 * i + 4)) (by decide)
    (by rw [u2.other .r3 (by decide)]; exact w1.ea a1 (by omega_using [hi, ha]))
    (by rw [u2.rd, u2.wr]; exact w1.read (by omega_using [hi, ha])) fun s3 u3 => ?_
  obtain k3 : Rest [.r1, .r3, .r9] s s3 :=
    (u1.rest (by decide)).trans ((u2.rest (by decide)).trans (u3.rest (by decide)))
  obtain m3 : s3.mem = s.mem := u3.mem.trans (u2.mem.trans u1.mem)
  obtain p3 : s3.gpr .r0 = base + BitVec.ofNat 32 tmp := (k3.gpr .r0 (by decide)).trans ptr
  obtain w3 := ws.congr k3.wr
  refine wp_ldr (by decide) (w3.ea p3 (by omega_using [ht])) (w3.read (by omega_using [ht])) fun s4 u4 => ?_
  obtain p4 : s4.gpr .r0 = base + BitVec.ofNat 32 tmp := (u4.other .r0 (by decide)).trans p3
  refine wp_ldr (by decide) ((w3.congr u4.wr).ea p4 (by omega_using [ht])) ((w3.congr u4.wr).read (by omega_using [ht]))
    fun s5 u5 => ?_
  obtain p5 : s5.gpr .r0 = base + BitVec.ofNat 32 tmp := (u5.other .r0 (by decide)).trans p4
  obtain w5 := (w3.congr u4.wr).congr u5.wr
  refine wp_ldr (by decide) (w5.ea p5 (by omega_using [ht])) (w5.read (by omega_using [ht])) fun s6 u6 => ?_
  obtain p6 : s6.gpr .r0 = base + BitVec.ofNat 32 tmp := (u6.other .r0 (by decide)).trans p5
  obtain w6 := w5.congr u6.wr
  refine wp_ldr (by decide) (w6.ea p6 (by omega_using [ht])) (w6.read (by omega_using [ht])) fun s7 u7 => ?_
  refine wp_mov (op2_reg _ .r2) fun s8 u8 => ?_
  obtain p8 : s8.gpr .r0 = base + BitVec.ofNat 32 tmp :=
    (u8.other .r0 (by decide)).trans ((u7.other .r0 (by decide)).trans p6)
  obtain w8 := (w6.congr u7.wr).congr u8.wr
  refine wp_ldr (by decide) (w8.ea p8 (by omega_using [ht])) (w8.read (by omega_using [ht])) fun s9 u9 => ?_
  refine wp_mov (op2_imm (by decide)) fun s10 u10 => ?_
  refine wp_mov (op2_imm (by decide)) fun s11 u11 => ?_
  refine wp_mov (op2_imm (by decide)) fun s12 u12 => ?_
  refine wp_mov (op2_imm (by decide)) fun t u13 => WP.block_nil ?_
  obtain mem9 : s9.mem = s.mem := by rw [u9.mem, u8.mem, u7.mem, u6.mem, u5.mem, u4.mem, m3]
  have tail (r : Reg) (h1 : r ≠ .r11) (h2 : r ≠ .r5) (h3 : r ≠ .r8) (h4 : r ≠ .r7) :
      t.gpr r = s9.gpr r := by
    rw [u13.other r h1, u12.other r h2, u11.other r h3, u10.other r h4]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, u13.gpr, ?_, ?_⟩
  · rw [tail .r1 (by decide) (by decide) (by decide) (by decide), u9.other .r1 (by decide),
      u8.other .r1 (by decide), u7.other .r1 (by decide), u6.other .r1 (by decide),
      u5.other .r1 (by decide), u4.other .r1 (by decide), u3.other .r1 (by decide), u2.gpr, u1.mem]
  · rw [tail .r9 (by decide) (by decide) (by decide) (by decide), u9.other .r9 (by decide),
      u8.other .r9 (by decide), u7.other .r9 (by decide), u6.other .r9 (by decide),
      u5.other .r9 (by decide), u4.other .r9 (by decide), u3.gpr, u2.mem, u1.mem]
  · rw [tail .r0 (by decide) (by decide) (by decide) (by decide), u9.gpr, u8.mem, u7.mem, u6.mem,
      u5.mem, u4.mem, m3, hdr.accPtr]
  · rw [tail .r12 (by decide) (by decide) (by decide) (by decide), u9.other .r12 (by decide),
      u8.other .r12 (by decide), u7.other .r12 (by decide), u6.other .r12 (by decide), u5.gpr,
      u4.mem, m3, hdr.bPtr]
  · rw [tail .r4 (by decide) (by decide) (by decide) (by decide), u9.other .r4 (by decide),
      u8.other .r4 (by decide), u7.other .r4 (by decide), u6.gpr, u5.mem, u4.mem, m3, hdr.mPtr]
  · rw [tail .r2 (by decide) (by decide) (by decide) (by decide), u9.other .r2 (by decide),
      u8.other .r2 (by decide), u7.gpr, u6.mem, u5.mem, u4.mem, m3, hdr.inverse]
  · rw [tail .r10 (by decide) (by decide) (by decide) (by decide), u9.other .r10 (by decide), u8.gpr,
      u7.gpr, u6.mem, u5.mem, u4.mem, m3, hdr.inverse]
  · rw [tail .lr (by decide) (by decide) (by decide) (by decide), u9.other .lr (by decide),
      u8.other .lr (by decide), u7.other .lr (by decide), u6.other .lr (by decide),
      u5.other .lr (by decide), u4.gpr, m3, Nat.add_zero, hdr.count]
  · rw [u13.other .r7 (by decide), u12.other .r7 (by decide), u11.other .r7 (by decide), u10.gpr]
  · rw [u13.other .r8 (by decide), u12.other .r8 (by decide), u11.gpr]
  · rw [u13.other .r5 (by decide), u12.gpr]
  · rw [u13.mem, u12.mem, u11.mem, u10.mem, mem9]
  · exact (k3.mono (by decide)).trans ((u4.rest (by decide)).trans
      ((u5.rest (by decide)).trans ((u6.rest (by decide)).trans
        ((u7.rest (by decide)).trans ((u8.rest (by decide)).trans
          ((u9.rest (by decide)).trans ((u10.rest (by decide)).trans
            ((u11.rest (by decide)).trans ((u12.rest (by decide)).trans
              (u13.rest (by decide)))))))))))

end VG.Proof.Bignum.Arm.Fios2

end

end

/-! `FiosTaint`'s analysis for any list of public registers: a UMAAL whose
outputs are not public forgets everything but them. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm.Fios2.Taint
open VG VG.Arm

def step (pub : List Reg) (τ : VG.Arm.Taint.T) (i : Instr) : Option VG.Arm.Taint.T :=
  match i with
  | .umaal lo hi _ _ =>
    if lo ∉ pub ∧ hi ∉ pub ∧ (RegSet.ofList pub).subset τ.regs = true then
      some (VG.Arm.Taint.ofRegs pub)
    else none
  | _ => taint.step τ i

private theorem umaal_keep {s t : State} {lo hi n m r : Reg}
    (hlo : r ≠ lo) (hhi : r ≠ hi) (h : exec (.umaal lo hi n m) s = some t) :
    t.gpr r = s.gpr r := by
  by_cases same : lo = hi
  · simp only [reduceExec, same, ite_true, reduceCtorEq] at h
  · simp only [reduceExec, same, ite_false, Option.some.injEq] at h
    subst t
    rw [RegUpd.gpr_setReg_of_ne _ _ hhi, RegUpd.gpr_setReg_of_ne _ _ hlo]

theorem sound (pub : List Reg) {τ τ' : VG.Arm.Taint.T} {i : Instr}
    {s₁ s₂ s₁' s₂' : State} (ha : VG.Arm.Taint.Agree τ s₁ s₂)
    (hs : step pub τ i = some τ')
    (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ VG.Arm.Taint.Agree τ' s₁' s₂' := by
  cases i with
  | mov | mvn | dp | adds | adc | subs | cmp | movw | movt | adrSym | rev | mul | mla | ldr | str | ldrb
    | strb | ldrSp | addSp | alloc | free | push | pop | blx =>
    exact taint.step_sound ha hs e₁ e₂
  | umaal lo hi n m =>
    change (if lo ∉ pub ∧ hi ∉ pub ∧ (RegSet.ofList pub).subset τ.regs = true then
      some (VG.Arm.Taint.ofRegs pub) else none) = some τ' at hs
    split at hs
    · rename_i keep
      simp only [Option.some.injEq] at hs
      subst τ'
      refine ⟨rfl, VG.Arm.Taint.agree_ofRegs ?_⟩
      intro r hr
      have hlo : r ≠ lo := by intro eq; subst r; exact keep.1 hr
      have hhi : r ≠ hi := by intro eq; subst r; exact keep.2.1 hr
      have old := ha.rf.1 r (RegSet.mem_of_subset keep.2.2 (RegSet.mem_ofList.mpr hr))
      rw [umaal_keep hlo hhi e₁, umaal_keep hlo hhi e₂]
      exact old
    · cases hs

/-- An untrusted analysis, proved against the execution model. -/
def analysis (pub : List Reg) : VG.Taint isa := { taint with step := step pub, step_sound := sound pub }

end VG.Proof.Bignum.Arm.Fios2.Taint
