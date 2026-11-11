module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePre
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.ABIResources
import VerifiedGarbage.Proof.Bignum.X86.CrtResources

/-! # `vg_rsa_private_crt_precomputed` on x86 against its contract

As `vg_rsa_private_crt` (`TimeTop.lean`), with `sized true` related by
`sizedNarrowP_relCT` from what each run keeps (`SideP`): constant time but
for the modulus and the pointer to `pre` (`constantTimeP`), and with
`correctP`, `verifiedP`.
-/

-- separate module: `vg_rsa_private_crt_precomputed`'s constant time builds in parallel with the wrapper's correctness (`PrivP.Fn`).

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.Crt (componentValue Pair)
open VG.Proof.Dsa.X86 (argumentPointer wp_result)
open VG.Proof.Bignum.X86.PublicRt (setWidth_toNat)

section
variable {s t : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {sp : BitVec 32}

/-- What each run keeps from the entry on, with `pre`: `Side`'s, `p q = n`, and each factor's cached
value if the factor is above one. -/
def SideP (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32) (s : State) : Prop :=
  Side base bytes len args sp s ∧
    componentValue s.mem args 6 * componentValue s.mem args 8 = componentValue s.mem args 2 ∧
    (1 < componentValue s.mem args 6 → PreR2 s base bytes len args 0 (componentValue s.mem args 6)) ∧
    (1 < componentValue s.mem args 8 → PreR2 s base bytes len args 1 (componentValue s.mem args 8)) ∧
    PreOut s args len 0 ∧ PreOut s args len 1

theorem SideP.keep (S : SideP base bytes len args sp s) {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp' : .esp ∉ regs) (m : t.mem = s.mem) : SideP base bytes len args sp t := by
  obtain ⟨S, pq, P0, P1, O0, O1⟩ := S
  refine ⟨S.keep K di sp' (by rw [m]; exact Outside.refl _ _ _ _), by rw [m]; exact pq, ?_, ?_, O0.keep K sp',
    O1.keep K sp'⟩
  · rw [m]; exact fun g => (P0 g).keepM K sp' m
  · rw [m]; exact fun g => (P1 g).keepM K sp' m

theorem sizedAtP_of (S : SideP base bytes len args sp s)
    (valid : Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true) :
    SizedAtP base bytes len args sp s := by
  obtain ⟨S, pq, P0, P1, O0, O1⟩ := S
  obtain ⟨odd, pN, qN⟩ := S.1.crt.factor_bounds valid
  obtain ⟨q1, qo⟩ := VG.Proof.Bignum.factor_facts pq pN odd
  obtain ⟨p1, po⟩ := VG.Proof.Bignum.factor_facts (by rw [Nat.mul_comm]; exact pq) qN odd
  refine ⟨⟨S.1, S.2.1, valid, S.2.2⟩, pq, ?_, ?_, O0, O1⟩
  · rw [safeM_of p1 po]; exact P0 p1
  · rw [safeM_of q1 qo]; exact P1 q1

theorem bodyP_relCT (sp : BitVec 32) :
    RelCT isa (fun s t => SideP base bytes len args sp s ∧ SideP base bytes len args sp t ∧
      Spec.Rsa.bytesAt s.mem (byteAddr (args 2)) len = Spec.Rsa.bytesAt t.mem (byteAddr (args 2)) len)
      (CrtRt.body true) (fun _ _ => True) := by
  let R := fun s t => (SideP base bytes len args sp s ∧ SideP base bytes len args sp t) ∧
    ∃ b : Bool, s.zf = some b ∧ t.zf = some b ∧
      (b = true → Spec.Rsa.modulusValid (componentValue s.mem args 2) len = true ∧
        Spec.Rsa.modulusValid (componentValue t.mem args 2) len = true)
  have Branch : RelCT isa R (.ite .e (CrtRt.sized true) PublicFn.failure) (fun _ _ => True) := by
    apply VG.RelCT.ite (M := isa) (c := .e) (P := R)
    · intro s t ⟨_, b, Zs, Zt, _⟩
      exact Zs.trans Zt.symm
    · intro s t tr ur sf tf ⟨⟨⟨S₁, S₂⟩, b, Zs, _, V⟩, Z⟩ E F
      have B : b = true := by
        change s.zf = some true at Z
        exact Option.some.inj (Zs.symm.trans Z)
      exact sizedNarrowP_relCT sp _ _ _ _ _ _ ⟨sizedAtP_of S₁ (V B).1, sizedAtP_of S₂ (V B).2⟩ E F
    · exact (Crt.failure_relCT base bytes len args).mono (fun _ _ H => H.1.1.1.1.pair H.1.1.2.1) (fun _ _ h => h)
  apply VG.RelCT.assoc
  intro s t tr ur sf tf ⟨S₁, S₂, N⟩ E F
  have modulus : ∀ {m : Mem} {x : State}, SideP base bytes len args sp x →
      componentValue m args 2 = Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2)) len) := by
    intro m x S
    unfold componentValue
    change Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (byteAddr (args 2)) (args 3).toNat) = _
    rw [S.1.1.crt.modulus_length]
  cases E with
  | @seq _ _ _ u _ _ _ E1 E2 =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 F2 =>
      have T1 := (Crt.modulus_relCT base bytes len args _ _ _ _ _ _ (S₁.1.pair S₂.1) E1 F1).1
      obtain ⟨Zs, Ms, Ks⟩ := wp_result (Crt.modulus_ok S₁.1.1.crt) E1
      obtain ⟨Zt, Mt, Kt⟩ := wp_result (Crt.modulus_ok S₂.1.1.crt) F1
      have U₁ := S₁.keep Ks (by decide) (by decide) Ms
      have U₂ := S₂.keep Kt (by decide) (by decide) Mt
      have Relation : R u v := ⟨⟨U₁, U₂⟩, _, Zs, by rw [N]; exact Zt, fun hb => ⟨?_, ?_⟩⟩
      · have T2 := (Branch _ _ _ _ _ _ Relation E2 F2).1
        exact ⟨by rw [T1, T2], trivial⟩
      · rw [modulus U₁, Ms]; exact hb
      · rw [modulus U₂, Mt, ← N]; exact hb


theorem PreR2.congrArgs {i p : Nat} {args' : Nat → BitVec 32} (P : PreR2 s base bytes len args i p)
    (e : ∀ j < 20, args' j = args j) : PreR2 s base bytes len args' i p := by
  have hi := P.hi
  have a7 := e 7 (by decide)
  have ai : args' (7 + 2 * i) = args (7 + 2 * i) := e _ (by omega)
  have aw : preW args' i = preW args i := by simp only [preW, ai]
  have ao : preOff args' i = preOff args i := by simp only [preOff, a7]
  have ap : args' preArg = args preArg := e _ (by decide)
  exact ⟨⟨P.arg.stack, by rw [ap]; exact P.arg.value⟩, P.hi, by rw [ai]; exact P.pos, by rw [ai]; exact P.lt,
    by rw [a7]; exact P.lt7, by rw [a7]; exact P.pos7, by rw [ap, ao, aw]; exact P.read,
    by rw [ap, ao, aw]; exact P.fit, by rw [ap, ao, aw]; exact P.apart, by rw [ap, ao, aw]; exact P.val, P.top,
    by rw [ap, ao, aw]; exact P.apartSp⟩

theorem PreOut.congrArgs {i : Nat} {args' : Nat → BitVec 32} (O : PreOut s args len i) (hi : i ≤ 1)
    (e : ∀ j < 20, args' j = args j) : PreOut s args' len i := by
  have a0 := e 0 (by decide)
  have a7 := e 7 (by decide)
  have ai : args' (7 + 2 * i) = args (7 + 2 * i) := e _ (by omega)
  have aw : preW args' i = preW args i := by simp only [preW, ai]
  have ao : preOff args' i = preOff args i := by simp only [preOff, a7]
  have ap : args' preArg = args preArg := e _ (by decide)
  exact ⟨by rw [a0]; exact O.arg, by rw [ap, ao, aw, a0]; exact O.val⟩

theorem componentValue_congr {m : Mem} {args' : Nat → BitVec 32} {i : Nat} (e : ∀ j < 20, args' j = args j)
    (hi : i + 1 < 20) : componentValue m args' i = componentValue m args i := by
  unfold componentValue; rw [e i (by omega), e (i + 1) hi]

theorem SideP.congrArgs {args' : Nat → BitVec 32} (S : SideP base bytes len args sp s)
    (e : ∀ j < 20, args' j = args j) : SideP base bytes len args' sp s := by
  obtain ⟨⟨h, esp, d0, d1⟩, pq, P0, P1, O0, O1⟩ := S
  have c : ∀ i, i + 1 < 20 → componentValue s.mem args' i = componentValue s.mem args i :=
    fun i hi => componentValue_congr e hi
  refine ⟨⟨In.ofInputs (h.crt.argsEq fun i hi => (e i (by omega)).symm) h.need
      (by rw [e 16 (by decide)]; exact h.hbase) (by rw [e 17 (by decide)]; exact h.hbytes), esp,
      by rw [e 0 (by decide)]; exact d0, d1⟩, ?_, ?_, ?_, O0.congrArgs (by decide) e, O1.congrArgs (by decide) e⟩
  · rw [c 6 (by decide), c 8 (by decide), c 2 (by decide)]; exact pq
  · rw [c 6 (by decide)]; exact fun g => (P0 g).congrArgs e
  · rw [c 8 (by decide)]; exact fun g => (P1 g).congrArgs e

end

theorem argumentsP {s t : State} (H : (privateCrtPrecomputedContract abi 96).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 20, arg s i = arg t i := by
  sig_pub [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots, argVal,
    argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem modulusBytesP {s t : State} (H : (privateCrtPrecomputedContract abi 96).pub s t) :
    Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat := by
  have Leak : (Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat).map (·.toNat) =
      (Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat).map (·.toNat) := by
    sig_pub [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots, argVal,
      argBytes] at H
    exact H.2.1
  exact (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak

/-- What each run keeps from the entry on, from the contract. -/
theorem sideP_entry {s u : State} (A : CrtABIP s)
    (I : Crt.Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) u)
    (K : Keeps [.eax, .edi] s u) (O : Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) s.mem u.mem) :
    SideP (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) u := by
  have R := A.res
  have need := need_le A.lengths.1 A.scratchLength
  have hb : (arg s 16).toNat = (argumentPointer s 16).toNat := (setWidth_toNat _).symm
  have espu : u.gpr .esp = s.gpr .esp := K.1 _ (by decide)
  have high : (arg s 17).toNat * 8 ≤ 2 ^ 64 := by have := A.scratchBound; omega
  have sub72 := pre_sub 72 80 (by decide) (argAddr s 0)
  have bound : (s.gpr .esp).toNat + 4 + 72 ≤ 2 ^ 32 := by have := A.stackBound; omega
  have B (i : Nat) (hi : i ∈ Crt.componentArguments) :
      Spec.Rsa.bytesAt u.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat =
        Spec.Rsa.bytesAt s.mem (byteAddr (arg s i)) (arg s (i + 1)).toNat := by
    apply VG.Proof.Bignum.scratch_bytes O (by have := (arg s (i + 1)).isLt; omega)
    simp only [Crt.componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact A.nScratch
    · exact A.inScratch
    · exact A.pScratch
    · exact A.qScratch
    · exact A.dpScratch
    · exact A.dqScratch
    · exact A.qiScratch
  have C (i : Nat) (hi : i ∈ Crt.componentArguments) :
      componentValue u.mem (arg s) i = componentValue s.mem (arg s) i := by
    unfold componentValue; rw [B i hi]
  have Fe : Frame [⟨argumentPointer s 16, (arg s 17).toNat * 8⟩] s.mem u.mem := by
    have F := VG.Proof.Bignum.outside_frame O (by omega)
    simpa only [off, BitVec.add_zero] using F
  have keepP : ∀ {i p : Nat}, PreR2 s (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) i p →
      PreR2 u (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) i p := fun P =>
    P.keep K (by decide) Fe (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).1)
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact (P.apart_sub fun _ h => h).2)
  refine ⟨⟨In.ofInputs I need hb rfl, espu, ?_, ?_⟩, ?_, ?_, ?_, (preOut_of A (i := 0) (by decide)).keep K (by decide),
    (preOut_of A (i := 1) (by decide)).keep K (by decide)⟩
  · rw [espu, ← A.outLength]
    exact VG.X86.Taint.frame_disjoint (n := 72) bound A.retOut (A.outArgs.symm.sub_left sub72)
  · rw [espu]
    exact VG.X86.Taint.frame_disjoint (n := 72) bound A.retScratch (A.scratchArgs.symm.sub_left sub72)
  · rw [C 6 (by decide), C 8 (by decide), C 2 (by decide)]; exact A.product
  · intro g; rw [C 6 (by decide)] at g ⊢; exact keepP (preR2_of A (i := 0) (by decide) g)
  · intro g; rw [C 8 (by decide)] at g ⊢; exact keepP (preR2_of A (i := 1) (by decide) g)

theorem operationP_trace {s t : State} (A : CrtABIP s) (B : CrtABIP t)
    (args : ∀ i < 20, arg s i = arg t i) (SP : s.gpr .esp = t.gpr .esp)
    (N : Spec.Rsa.bytesAt s.mem (argumentPointer s 2) (arg s 3).toNat =
      Spec.Rsa.bytesAt t.mem (argumentPointer t 2) (arg t 3).toNat)
    {tr ur : List Leak} {sf tf : State}
    (E : Exec isa (CrtRt.code true) s tr sf) (F : Exec isa (CrtRt.code true) t ur tf) : tr = ur := by
  have A2 := args 2 (by decide)
  have A3 := args 3 (by decide)
  have A8 := args 16 (by decide)
  have A9 := args 17 (by decide)
  cases E with
  | @seq _ _ _ u _ _ _ E1 Erest =>
    cases F with
    | @seq _ _ _ v _ _ _ F1 Frest =>
      have T1 := (Crt.entry_relCT _ _ _ _ _ _
        ⟨SP, A8, (A.res.args 16 (by decide)).readSrc, (B.res.args 16 (by decide)).readSrc⟩ E1 F1).1
      obtain ⟨Is, _, Ks, Os⟩ := wp_result (Crt.installedG_ok A.res) E1
      obtain ⟨It, _, Kt, Ot⟩ := wp_result (Crt.installedG_ok B.res) F1
      have Iv : Crt.Inputs (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) v := by
        have J := It.argsEq (fun i hi => (args i (by omega)).symm)
        simpa only [argumentPointer, ← A8, ← A9, ← A3] using J
      have Ov : VG.Proof.Mont.Outside (argumentPointer s 16) 0 ((arg s 17).toNat * 8) t.mem v.mem := by
        simpa only [argumentPointer, ← A8, ← A9] using Ot
      have Su := sideP_entry A Is Ks Os
      have Sv : SideP (argumentPointer s 16) ((arg s 17).toNat * 8) (arg s 3).toNat (arg s) (s.gpr .esp) v := by
        have S := (sideP_entry B It Kt Ot).congrArgs (args' := arg s) args
        simpa only [argumentPointer, ← A8, ← A9, ← A3, ← SP] using S
      have Ns := scratch_bytes Os (by have := A.lengths.2; omega) (Is.apart 2 (by decide))
      have Nt := scratch_bytes Ov (by have := A.lengths.2; omega) (Iv.apart 2 (by decide))
      have NN : Spec.Rsa.bytesAt u.mem (byteAddr (arg s 2)) (arg s 3).toNat =
          Spec.Rsa.bytesAt v.mem (byteAddr (arg s 2)) (arg s 3).toNat := by
        rw [Ns, Nt]
        simpa only [argumentPointer, byteAddr, ← A2, ← A3] using N
      cases Erest with
      | @seq _ _ _ w _ _ _ E2 E3 =>
        cases Frest with
        | @seq _ _ _ z _ _ _ F2 F3 =>
          have T2 := (bodyP_relCT (s.gpr .esp) _ _ _ _ _ _ ⟨Su, Sv, NN⟩ E2 F2).1
          obtain ⟨_, Ksu⟩ := wp_result (bodyP_ok Su.1.1 Su.2.1 Su.2.2.1 Su.2.2.2.2.1 Su.2.2.2.1 Su.2.2.2.2.2) E2
          obtain ⟨_, Ktv⟩ := wp_result (bodyP_ok Sv.1.1 Sv.2.1 Sv.2.2.1 Sv.2.2.2.2.1 Sv.2.2.2.1 Sv.2.2.2.2.2) F2
          have Agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) w z :=
            agree_regs (by
              intro r hr
              obtain rfl := List.mem_singleton.mp hr
              rw [Ksu.1 _ (by decide), Ktv.1 _ (by decide)]
              exact (Su.1.pair Sv.1).agree.rf.1 _ (by decide))
          have T3 := (Crt.restore_relCT _ _ _ _ _ _ Agree E3 F3).1
          rw [T1, T2, T3]

theorem constantTimeP : ConstantTime isa (privateCrtPrecomputedContract abi 96).pre
    (privateCrtPrecomputedContract abi 96).pub (CrtRt.code true) := by
  intro s t tr ur sf tf S T H E F
  have Args := argumentsP H
  exact operationP_trace (crtABIP_of S) (crtABIP_of T) Args.2 Args.1 (modulusBytesP H) E F

/-- `satState` with `pre`'s four zero words, the values of the zero factors. -/
def satStateP : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x20005 then 16
    else if a = 0x20008 then 64
    else if a = 0x2000d then 32
    else if a = 0x20010 then 64
    else if a = 0x20015 then 48
    else if a = 0x20018 then 64
    else if a = 0x2001d then 64
    else if a = 0x20020 then 1
    else if a = 0x20025 then 80
    else if a = 0x20028 then 1
    else if a = 0x2002d then 96
    else if a = 0x20030 then 1
    else if a = 0x20035 then 112
    else if a = 0x20038 then 1
    else if a = 0x2003d then 128
    else if a = 0x20040 then 1
    else if a = 0x20045 then 144
    else if a = 0x20048 then 32
    else if a = 0x20049 then 4
    else if a = 0x2004d then 0xc0
    else if a = 0x20050 then 4 else 0
  rd := [⟨8192, 64⟩, ⟨12288, 64⟩, ⟨16384, 1⟩, ⟨20480, 1⟩, ⟨24576, 1⟩, ⟨28672, 1⟩, ⟨32768, 1⟩, ⟨49152, 32⟩]
  wr := [⟨4096, 64⟩, ⟨36864, 8448⟩, ⟨0x20004, 80⟩]

/-- The arguments of `satStateP`. -/
def satArgP (j : Nat) : BitVec 32 :=
  if j = 0 then 4096 else if j = 1 then 64 else if j = 2 then 8192 else if j = 3 then 64
  else if j = 4 then 12288 else if j = 5 then 64 else if j = 6 then 16384 else if j = 7 then 1
  else if j = 8 then 20480 else if j = 9 then 1 else if j = 10 then 24576 else if j = 11 then 1
  else if j = 12 then 28672 else if j = 13 then 1 else if j = 14 then 32768 else if j = 15 then 1
  else if j = 16 then 36864 else if j = 17 then 1056 else if j = 18 then 49152 else 4

theorem satP_pre_of {s : State} (hsp : s.gpr .esp = 0x20000) (ha : ∀ j < 20, arg s j = satArgP j)
    (hrd : s.rd = satStateP.rd) (hwr : s.wr = satStateP.wr)
    (hk : Spec.Rsa.wordsAt s.mem 49152 4 =
      Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem 16384 1) ++ Spec.Rsa.primeR2 (Spec.Rsa.bytesAt s.mem 20480 1))
    (hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem 16384 1) * Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem 20480 1) =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem 8192 64)) :
    (privateCrtPrecomputedContract abi 96).pre s := by
  have e : argAddr s 0 = 0x20004 := by simp only [argAddr, hsp]; rfl
  sig_pre [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots,
      argVal, argBytes, stackBelow]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), hsp, hrd, hwr, e, satArgP,
    Nat.reduceEqDiff, ↓reduceIte]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact hk
    | exact hp
    | (simp only [Spec.Rsa.lenValid]; decide)

theorem satP_args : ∀ j < 20, arg satStateP j = satArgP j := by decide

theorem satP_words : Spec.Rsa.wordsAt satStateP.mem 49152 4 =
    Spec.Rsa.primeR2 (Spec.Rsa.bytesAt satStateP.mem 16384 1) ++
      Spec.Rsa.primeR2 (Spec.Rsa.bytesAt satStateP.mem 20480 1) := by
  decide +kernel

theorem satP_product : Spec.Rsa.os2ip (Spec.Rsa.bytesAt satStateP.mem 16384 1) *
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt satStateP.mem 20480 1) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt satStateP.mem 8192 64) := by
  decide +kernel

theorem satisfiableP : ∃ s, (privateCrtPrecomputedContract abi 96).pre s :=
  ⟨satStateP, satP_pre_of rfl satP_args rfl rfl satP_words satP_product⟩

theorem verifiedP : Verified target (CrtRt.code true) (privateCrtPrecomputedContract abi 96) :=
  ⟨correctP, constantTimeP, satisfiableP⟩

end VG.Proof.Bignum.X86.CrtRt
