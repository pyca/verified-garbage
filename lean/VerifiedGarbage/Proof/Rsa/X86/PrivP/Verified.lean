module

public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Fn
public import VerifiedGarbage.Proof.Rsa.X86.PrivP.Contract
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
public import VerifiedGarbage.Proof.Rsa.X86.PrivStages
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Rsa.X86.PrivBodyTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivFnTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Rsa.X86.PrivObservations
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Rsa.X86.PrivInstances
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTopP
import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety

/-! # `vg_rsa_private_checked_precomputed` on x86: correct, constant time, verified

Correct (`private_contractP_correct`), constant time (`private_contractP_ct`),
satisfiable (`satisfiableP`) and so `Verified` (`code_verifiedP`); its stack and
stack-pointer safety, and the `vg_rsa_private_crt_precomputed` it calls
(`crtPBaseline`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86

theorem private_contractP_correct (v : CrtImpl) (w : CrtPImpl) (s : State)
    (h : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s) :
    ∃ tr t, Exec isa (privCodeP v w) s tr t ∧ abiPreserved s t ∧
      (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).post s t := by
  obtain ⟨I, H⟩ := private_contractP_pre h
  obtain ⟨tr, t, run, preserved, post⟩ := privateFnP_ok v w s I H
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact post
end VG.Proof.Rsa.X86.PrivChecked

/-! ## constant time

`vg_rsa_private_checked`'s argument, of the same `pre` and `pre_len` in both runs
(`privateBodyP_relCT`, `privateFnP_relCT`, `private_contractP_ct`).
-/

namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked VG.Proof.Bignum.X86
open VG.Proof.Dsa.X86 (allocated)

section
variable {g : PrivGeometry} {P : BitVec 32} {L : Nat}

theorem crtArgsP_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block (crtArgs ++ preR2Args))
    (VG.X86.Taint.Agree (τr [.esp])) := VG.Proof.Dsa.X86.checkedBlockInvariant rfl rfl

/-- Before the call of `vg_rsa_private_crt_precomputed`. -/
structure CrtReadyP (g : PrivGeometry) (bs : Fin 8 → List Byte) (P : BitVec 32) (L : Nat) (s : State) : Prop
    extends PrivateState g bs s where
  pre : PreCtx g bs P L s
  args : CrtArgsP g P L s

theorem crtArgsP_ready (s : State) {bs : Fin 8 → List Byte} (h : PrivateState g bs s ∧ PreCtx g bs P L s) :
    WP isa (.block (crtArgs ++ preR2Args)) s (CrtReadyP g bs P L) := by
  refine WP.mono (crtArgsP_ok s h.1.context h.2) ?_
  rintro t ⟨ht, Ht, args, _, _⟩
  exact ⟨⟨ht⟩, Ht, args⟩

theorem crtCallP_ready (w : CrtPImpl) (s : State) {bs : Fin 8 → List Byte} (h : CrtReadyP g bs P L s) :
    WP isa (.call w.name w.code) s (PrivateState g bs) := by
  refine WP.mono (crtP_call w h.context h.pre h.args) ?_
  rintro t ⟨ht, _, _, _, _⟩
  exact ⟨ht⟩

theorem crtCallP_pub {bs1 bs2 : Fin 8 → List Byte} {s t : State}
    (hs : PrivContext g bs1 s) (ht : PrivContext g bs2 t) (argsS : CrtArgsP g P L s) (argsT : CrtArgsP g P L t)
    (nb : bs1 0 = bs2 0) :
    (privateCrtPrecomputedContract abi 96).pub (s.callEntry.withRegions (crtRdP g P L) (crtWrP g))
      (t.callEntry.withRegions (crtRdP g P L) (crtWrP g)) := by
  sig_pub [privateCrtPrecomputedContract, privateCrtPrecomputedSig, Proof.Rsa.privateCrtSig, abi, argSlots,
    argVal, argBytes]
  have sa := fun {j} (hj : j < 20) => crtArgsP_values hs argsS hj
  have ta := fun {j} (hj : j < 20) => crtArgsP_values ht argsT hj
  simp only [hs.sp, ht.sp, sa (by decide : 0 < 20), ta (by decide : 0 < 20),
    sa (by decide : 1 < 20), ta (by decide : 1 < 20),
    sa (by decide : 2 < 20), ta (by decide : 2 < 20),
    sa (by decide : 3 < 20), ta (by decide : 3 < 20),
    sa (by decide : 4 < 20), ta (by decide : 4 < 20),
    sa (by decide : 5 < 20), ta (by decide : 5 < 20),
    sa (by decide : 6 < 20), ta (by decide : 6 < 20),
    sa (by decide : 7 < 20), ta (by decide : 7 < 20),
    sa (by decide : 8 < 20), ta (by decide : 8 < 20),
    sa (by decide : 9 < 20), ta (by decide : 9 < 20),
    sa (by decide : 10 < 20), ta (by decide : 10 < 20),
    sa (by decide : 11 < 20), ta (by decide : 11 < 20),
    sa (by decide : 12 < 20), ta (by decide : 12 < 20),
    sa (by decide : 13 < 20), ta (by decide : 13 < 20),
    sa (by decide : 14 < 20), ta (by decide : 14 < 20),
    sa (by decide : 15 < 20), ta (by decide : 15 < 20),
    sa (by decide : 16 < 20), ta (by decide : 16 < 20),
    sa (by decide : 17 < 20), ta (by decide : 17 < 20),
    sa (by decide : 18 < 20), ta (by decide : 18 < 20),
    sa (by decide : 19 < 20), ta (by decide : 19 < 20),
    crtArgumentP, crtArgument, PrivGeometry.argument, Nat.reduceAdd, Nat.reduceLT, Nat.reduceEqDiff, ite_true,
    ite_false, true_and, and_true]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hs.valid.maxLength; omega : g.length < 2 ^ 32)]
  have bytes : Spec.Rsa.bytesAt s.callEntry.mem ((g.sources 0).setWidth 64) g.length =
      Spec.Rsa.bytesAt t.callEntry.mem ((g.sources 0).setWidth 64) g.length :=
    (hs.callBytes 0).trans (nb.trans (ht.callBytes 0).symm)
  simp only [State.callEntry_mem, hs.sp, ht.sp] at bytes
  rw [bytes]

theorem crtCallP_ct (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte} (nb : bs1 0 = bs2 0) :
    RelCT isa (fun s t => CrtReadyP g bs1 P L s ∧ CrtReadyP g bs2 P L t) (.call w.name w.code)
      (fun _ _ => True) := by
  apply RelCT.call w.verified.1 w.verified.2.1 (crtRdP g P L) (crtWrP g)
  intro s t h
  exact ⟨crtCallP_pre h.1.context h.1.pre h.1.args, crtCallP_pre h.2.context h.2.pre h.2.args,
    crtCallP_pub h.1.context h.2.context h.1.args h.2.args nb,
    (crtCoversP h.1.context h.1.pre).1, (crtCoversP h.1.context h.1.pre).2,
    (crtCoversP h.2.context h.2.pre).1, (crtCoversP h.2.context h.2.pre).2, h.1.context.sp.trans h.2.context.sp.symm⟩

theorem privateBodyP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (PrivateState g bs1 s ∧ PreCtx g bs1 P L s) ∧ (PrivateState g bs2 t ∧ PreCtx g bs2 P L t))
      (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) (fun _ _ => True) := by
  unfold bodyP
  apply pair_seq_ct (crtArgsP_relCT.mono
    (fun _ _ h => sp_agree (h.1.1.context.sp.trans h.2.1.context.sp.symm)) (fun _ _ _ => trivial))
    (fun s h => crtArgsP_ready s h) (fun s h => crtArgsP_ready s h)
  exact pair_seq_ct (crtCallP_ct w nb) (fun s h => crtCallP_ready w s h) (fun s h => crtCallP_ready w s h)
    (privateCheck_relCT v nb eb)

theorem privateAllocationP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun a b => ∃ s t, (PrivFnInput g bs1 s ∧ PreCtx g bs1 P L (entered s)) ∧
      (PrivFnInput g bs2 t ∧ PreCtx g bs2 P L (entered t)) ∧
      a = pushed savedRegisters s ∧ b = pushed savedRegisters t)
      (.frame (.alloc VG.Impl.Rsa.X86.PrivChecked.frameBytes)
        (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) (.free VG.Impl.Rsa.X86.PrivChecked.frameBytes))
      (fun a b => a.gpr .esp = b.gpr .esp) := by
  intro a b ta tb a' b' hp ea eb'
  obtain ⟨s, t, ⟨hs, Hs⟩, ⟨ht, Ht⟩, rfl, rfl⟩ := hp
  have sp : (pushed savedRegisters s).gpr .esp = (pushed savedRegisters t).gpr .esp := by
    rw [hs.savedSp, ht.savedSp]
  have post : a'.gpr .esp = b'.gpr .esp := by
    rw [Exec.gpr (privateAllocationP_noSp v w) ea, Exec.gpr (privateAllocationP_noSp v w) eb', sp]
  cases ea with
  | frame pa ba _ =>
    cases eb' with
    | frame pb bb _ =>
      have ha := allocation_state pa
      have hb := allocation_state pb
      subst ha hb
      have eq := (privateBodyP_relCT v w nb eb) _ _ _ _ _ _ ⟨⟨⟨hs.context⟩, Hs⟩, ⟨⟨ht.context⟩, Ht⟩⟩ ba bb
      refine ⟨?_, post⟩
      rw [eq.1]
      rfl

theorem privateFnP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (PrivFnInput g bs1 s ∧ PreCtx g bs1 P L (entered s)) ∧
      (PrivFnInput g bs2 t ∧ PreCtx g bs2 P L (entered t)))
      (privCodeP v w) (fun _ _ => True) := by
  unfold privCodeP codeP
  refine RelCT.frame (R := fun _ _ => True) ?_ ?_
  · intro s t h
    have eq := h.1.1.savedSp.trans h.2.1.savedSp.symm
    rw [pushed_esp, pushed_esp] at eq
    have same := congrArg (fun x => x + BitVec.ofNat 32 (4 * savedRegisters.length)) eq
    simpa only [BitVec.sub_add_cancel] using same
  · refine VG.RelCT.seq ((privateAllocationP_relCT v w (g := g) (P := P) (L := L) nb eb).mono ?_ (fun _ _ h => h))
      (restore_relCT.mono (fun _ _ h => sp_agree h) (fun _ _ _ => trivial))
    rintro a b ⟨s, t, h, rfl, rfl⟩
    exact ⟨s, t, h.1, h.2, rfl, rfl⟩
end

/-! ## The contract's public arguments -/

theorem argumentsP {s t : State} (H : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 22, arg s i = arg t i := by
  sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
        i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 := by
      omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicBytesP {s t : State} (H : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pub s t) :
    privateBytes s 0 = privateBytes t 0 ∧ privateBytes s 1 = privateBytes t 1 := by
  have Args := argumentsP H
  have Leak : ((privateBytes s 0) ++ (privateBytes s 1)).map (·.toNat) =
      ((privateBytes t 0) ++ (privateBytes t 1)).map (·.toNat) := by
    sig_pub [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
      Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes] at H
    have L := H.2.1
    rw [List.map_append, List.map_append] at L
    have len : ((Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat).map (·.toNat) ++
        (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat).map (·.toNat)).length =
        ((Spec.Rsa.bytesAt t.mem ((arg t 2).setWidth 64) (arg t 3).toNat).map (·.toNat) ++
        (Spec.Rsa.bytesAt t.mem ((arg t 4).setWidth 64) (arg t 5).toNat).map (·.toNat)).length := by
      simp only [List.length_append, List.length_map, Spec.Rsa.bytesAt, List.length_range,
        Args.2 3 (by decide), Args.2 5 (by decide)]
    simpa only [List.map_append, privateBytes, privateGeometry, PrivGeometry.sourceLength,
      Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd,
      VG.Proof.Bignum.X86.byteAddr] using List.append_inj_left L len
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak
  have sameLength : (privateBytes s 0).length = (privateBytes t 0).length := by
    simp only [privateBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (arg s 3).toNat = (arg t 3).toNat
    rw [Args.2 3 (by decide)]
  exact ⟨List.append_inj_left both sameLength, List.append_inj_right both sameLength⟩

theorem publicGeometryP {s t : State} (H : (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pub s t) :
    privateGeometry s = privateGeometry t := by
  obtain ⟨sp, args⟩ := argumentsP H
  have sources : (fun i : Fin 8 => arg s (2 + 2 * i.val)) =
      (fun i : Fin 8 => arg t (2 + 2 * i.val)) := by
    funext i
    exact args _ (by omega)
  simp only [privateGeometry, sp, sources, args 0 (by decide), args 18 (by decide),
    args 3 (by decide), args 5 (by decide), args 9 (by decide), args 11 (by decide), args 19 (by decide)]

theorem private_contractP_ct (v : CrtImpl) (w : CrtPImpl) :
    ConstantTime isa (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre
      (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pub (privCodeP v w) := by
  intro s t tr1 tr2 u u' hs ht hp e1 e2
  obtain ⟨Is, Hs⟩ := private_contractP_pre hs
  obtain ⟨It, Ht⟩ := private_contractP_pre ht
  obtain ⟨nb, eb⟩ := publicBytesP hp
  have geometry := publicGeometryP hp
  rw [← geometry] at It Ht
  rw [← (argumentsP hp).2 20 (by decide), ← (argumentsP hp).2 21 (by decide)] at Ht
  exact (privateFnP_relCT v w nb eb s t tr1 tr2 u u' ⟨⟨Is, Hs⟩, ⟨It, Ht⟩⟩ e1 e2).1
end VG.Proof.Rsa.X86.PrivChecked

/-! ## the certificate

Satisfiable by a key of a 512-bit modulus `n = 129 (2^504 - 1)` (`satisfiableP`):
`privatePrecompute` asks for a valid modulus whose factors multiply to it.
-/

namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86

/-- `q = 2^504 - 1`, 63 octets. -/
def satQ : Nat := 2 ^ 504 - 1
/-- `n = 129 q`, 64 octets, odd, of 512 bits. -/
def satN : Nat := 129 * satQ
/-- `privatePrecompute n 129 q`'s 26 words, least significant first, as one number. -/
def satPre : Nat :=
  satN + (2 ^ 1024 % satN) * 2 ^ 512 + (2 ^ 256 % 129) * 2 ^ 1024 + (2 ^ 1024 % satQ) * 2 ^ 1152

/-- The arguments of `satStateQ`. -/
def satArgQ (j : Nat) : BitVec 32 :=
  if j = 0 then 4096
  else if j = 1 then 64
  else if j = 2 then 8192
  else if j = 3 then 64
  else if j = 4 then 12288
  else if j = 5 then 1
  else if j = 6 then 16384
  else if j = 7 then 64
  else if j = 8 then 20480
  else if j = 9 then 1
  else if j = 10 then 24576
  else if j = 11 then 63
  else if j = 12 then 28672
  else if j = 13 then 1
  else if j = 14 then 32768
  else if j = 15 then 63
  else if j = 16 then 36864
  else if j = 17 then 1
  else if j = 18 then 40960
  else if j = 19 then 1056
  else if j = 20 then 53248
  else 26

/-- Disjoint buffers of a 64-octet modulus, its factors 129 and `q`, and `pre`. -/
def satStateQ : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a :=
    if 0x20004 ≤ a.toNat ∧ a.toNat < 0x20004 + 88 then
      (satArgQ ((a.toNat - 0x20004) / 4) >>> (8 * ((a.toNat - 0x20004) % 4))).setWidth 8
    else if 8192 ≤ a.toNat ∧ a.toNat < 8192 + 64 then BitVec.ofNat 8 (satN / 2 ^ (8 * (8255 - a.toNat)))
    else if a.toNat = 20480 then 129
    else if 24576 ≤ a.toNat ∧ a.toNat < 24576 + 63 then 0xff
    else if 53248 ≤ a.toNat ∧ a.toNat < 53248 + 208 then BitVec.ofNat 8 (satPre / 2 ^ (8 * (a.toNat - 53248)))
    else 0
  rd := [⟨8192, 64⟩, ⟨12288, 1⟩, ⟨16384, 64⟩, ⟨20480, 1⟩, ⟨24576, 63⟩, ⟨28672, 1⟩, ⟨32768, 63⟩,
    ⟨36864, 1⟩, ⟨53248, 208⟩]
  wr := [⟨4096, 64⟩, ⟨40960, 8448⟩, ⟨0x20004, 88⟩]

theorem satQ_pre_of {s : State} (hsp : s.gpr .esp = 0x20000) (ha : ∀ j < 22, arg s j = satArgQ j)
    (hrd : s.rd = satStateQ.rd) (hwr : s.wr = satStateQ.wr)
    (hk : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 8192 64) (Spec.Rsa.bytesAt s.mem 20480 1)
      (Spec.Rsa.bytesAt s.mem 24576 63) = some (Spec.Rsa.wordsAt s.mem 53248 26)) :
    (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s := by
  have e : argAddr s 0 = 0x20004 := by simp only [argAddr, hsp]; rfl
  sig_pre [Proof.Rsa.privateCheckedPrecomputedContract, Proof.Rsa.privateCheckedPrecomputedSig,
    Proof.Rsa.privateCheckedSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide), ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), ha 16 (by decide), ha 17 (by decide), ha 18 (by decide), ha 19 (by decide), ha 20 (by decide), ha 21 (by decide), hsp, hrd, hwr, e, satArgQ, Nat.reduceEqDiff, ↓reduceIte]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | exact hk
    | (simp only [Spec.Rsa.lenValid]; decide)

theorem satQ_args : ∀ j < 22, arg satStateQ j = satArgQ j := by decide

theorem satQ_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt satStateQ.mem 8192 64)
    (Spec.Rsa.bytesAt satStateQ.mem 20480 1) (Spec.Rsa.bytesAt satStateQ.mem 24576 63) =
      some (Spec.Rsa.wordsAt satStateQ.mem 53248 26) := by
  decide +kernel

theorem satisfiableP : ∃ s, (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes).pre s :=
  ⟨satStateQ, satQ_pre_of rfl satQ_args rfl rfl satQ_key⟩

theorem code_verifiedP (v : CrtImpl) (w : CrtPImpl) :
    Verified target (privCodeP v w) (Proof.Rsa.privateCheckedPrecomputedContract abi stackBytes) :=
  ⟨private_contractP_correct v w, private_contractP_ct v w, satisfiableP⟩
end VG.Proof.Rsa.X86.PrivChecked

/-! ## stack and instance

Its stack and its code's stack-pointer safety (`code_stackP`, `privateCodeP_noSp`), and the
`vg_rsa_private_crt_precomputed` it calls (`crtPBaseline`).
-/

namespace VG.Proof.Rsa.X86.PrivChecked
open VG VG.X86 VG.Impl.Rsa.X86.PrivChecked

/-- `vg_rsa_private_crt_precomputed`, `CrtRt.code true`. -/
def crtPBaseline : CrtPImpl where
  name := "vg_rsa_private_crt_precomputed"
  code := Impl.Bignum.X86.CrtRt.code true
  verified := Bignum.X86.CrtRt.verifiedP
  stack := by rw [RtShape.privateCrtP_stack]
  noSp := allStack_noSp RtShape.privateCrtP_spSafe

theorem privateCodeP_noSp (v : CrtImpl) (w : CrtPImpl) : NoSp (privCodeP v w) := by
  intro i hi
  change i ∈ instrs (.frame (.push savedRegisters)
    (.seq (.frame (.alloc VG.Impl.Rsa.X86.PrivChecked.frameBytes)
      (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) (.free VG.Impl.Rsa.X86.PrivChecked.frameBytes))
      (.block restore)) (.pop .ebx 4)) at hi
  simp only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | hi) | rfl
  · rfl
  · apply privateInnerP_noSp v w i
    simpa only [instrs, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] using hi
  · rfl

theorem code_spSafeP (v : CrtImpl) (w : CrtPImpl) : (privCodeP v w).all (fun i => !isa.writesSp i) = true :=
  noSp_allStack (privateCodeP_noSp v w)

theorem code_stackP (v : CrtImpl) (w : CrtPImpl) : stackUse (privCodeP v w) ≤ stackBytes := by
  have crt := w.stack
  have pc := v.pcStack
  have pd := v.pdStack
  have bound : stackUse (bodyP w.name w.code v.pcName v.pc v.pdName v.pd) ≤ 100 := by
    simp only [bodyP, check, tail, compareBytes, release, releaseLoop, stackUse, Nat.max_le]
    repeat apply And.intro
    all_goals omega
  simp only [privCodeP, codeP, stackUse, VG.X86.frameBytes, List.length_cons, List.length_nil,
    VG.Impl.Rsa.X86.PrivChecked.frameBytes, stackBytes]
  omega
end VG.Proof.Rsa.X86.PrivChecked
