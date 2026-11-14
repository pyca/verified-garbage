module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignP.Contract
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBodyTiming
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Spec.Weierstrass
public import VerifiedGarbage.Proof.Rsa.PreKey
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEraseTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignBlocksTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignFnTiming
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignEncArgs
import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignObservations
import VerifiedGarbage.Proof.Rsa.X86.PrivSetupTiming
import VerifiedGarbage.Proof.Rsa.X86.PrivReleaseTiming
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-! # `vg_rsa_pkcs1_sign_precomputed` on i686: correct, constant time, verified

Correct (`sign_contractP_correct`) and constant time (`sign_contractP_ct`):
`vg_rsa_pkcs1_sign`'s argument, with `pre`'s facts (`SPreCtx`) carried to the
call of `vg_rsa_private_checked_precomputed`, of the same `pre` and `pre_len`
in both runs. With `vg_rsa_pkcs1_sign`'s satisfiability (`satisfiablePre`),
`Verified` (`signPrecomputed_verified`).
-/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Sgn
open VG VG.X86 VG.X86.Wp VG.Proof.Bignum.X86 VG.Proof.Mont.X86 VG.Impl.RsaPkcs1Sig.X86.Sign VG.Proof.Dsa.X86
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl CrtPImpl privCodeP crtPBaseline sp_agree pair_seq_ct)

theorem sign_contractP_correct (v : CrtImpl) (w : CrtPImpl) (s : State)
    (h : (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre s) :
    ∃ tr t, Exec isa (code (privNameP v) (privCodeP v w) callArgsP) s tr t ∧
      abiPreserved s t ∧ (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).post s t := by
  obtain ⟨I, H⟩ := sign_contractP_pre h
  obtain ⟨tr, t, run, preserved, post⟩ := signFnP_ok v w s I H
  refine ⟨tr, t, run, preserved, ?_⟩
  sig_post [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes]
  rw [BitVec.setWidth_append_eq_right]
  exact post

/-! ## Constant time -/

section
variable {g : Geometry} {P : BitVec 32} {L : Nat}

structure CallReadyP (g : Geometry) (bs : Fin 8 → List Byte) (P : BitVec 32) (L : Nat) (s : State) : Prop where
  context : Context g bs s
  pre : SPreCtx g bs P L s
  args : PrivateArgsP g P L s

theorem callArgsP_relCT : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block callArgsP)
    (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl

theorem callArgsP_ready {bs : Fin 8 → List Byte} {s : State} (h : Context g bs s ∧ SPreCtx g bs P L s) :
    WP isa (.block callArgsP) s (CallReadyP g bs P L) := by
  refine WP.mono (callArgsP_ok h.1 h.2) ?_
  rintro t ⟨ht, Ht, args, _, _⟩
  exact ⟨ht, Ht, args⟩

theorem privateCallP_ready (v : CrtImpl) (w : CrtPImpl) {bs : Fin 8 → List Byte} {s : State}
    (h : CallReadyP g bs P L s) :
    WP isa (.call (privNameP v) (privCodeP v w)) s (Context g bs) := by
  refine WP.mono (private_callP v w h.context h.pre h.args rfl) ?_
  rintro t ⟨ht, _, _, _, _⟩
  exact ht

theorem privateCallP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => CallReadyP g bs1 P L s ∧ CallReadyP g bs2 P L t)
      (.call (privNameP v) (privCodeP v w)) (fun _ _ => True) := by
  have verified := VG.Proof.Rsa.X86.PrivChecked.code_verifiedP v w
  apply RelCT.call verified.1 verified.2.1 (privateRdP g P L) (privateWrP g)
  intro s t h
  exact ⟨privateCallP_pre h.1.context h.1.pre h.1.args, privateCallP_pre h.2.context h.2.pre h.2.args,
    privateCallP_pub h.1.context h.2.context h.1.pre h.2.pre h.1.args h.2.args nb eb,
    (privateCoversP h.1.context h.1.pre).1, (privateCoversP h.1.context h.1.pre).2,
    (privateCoversP h.2.context h.2.pre).1, (privateCoversP h.2.context h.2.pre).2,
    h.1.context.sp.trans h.2.context.sp.symm⟩

theorem callThenWipeP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (Context g bs1 s ∧ SPreCtx g bs1 P L s) ∧ (Context g bs2 t ∧ SPreCtx g bs2 P L t))
      (.seq (.block callArgsP) (.seq (.call (privNameP v) (privCodeP v w)) wipe)) (fun _ _ => True) := by
  apply pair_seq_ct (callArgsP_relCT.mono
    (fun _ _ h => sp_agree (h.1.1.sp.trans h.2.1.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => callArgsP_ready h) (fun _ h => callArgsP_ready h)
  exact pair_seq_ct (privateCallP_relCT v w nb eb) (fun _ h => privateCallP_ready v w h)
    (fun _ h => privateCallP_ready v w h) wipe_relCT

theorem compareP_ready {bs : Fin 8 → List Byte} {s : State} (h : EncodeDone g bs s ∧ SPreCtx g bs P L s) :
    WP isa (.block [.alu .cmp .eax (.imm 0)]) s (fun t => Compared g bs t ∧ SPreCtx g bs P L t) := by
  refine wp_cmpS rfl fun t F Z => WP.block_nil ?_
  refine ⟨⟨⟨h.1.context.after (by rw [F.mem]; exact Frame.refl _ _) (F.keeps []) (by rw [F.gpr]), ?_⟩, ?_⟩,
    h.2.after (by rw [F.mem]; exact Frame.refl _ _) (F.keeps [])⟩
  · simpa only [Encoded, F.gpr, F.mem] using h.1.encoded
  · rw [Z, F.gpr]
    exact congrArg some (by change (s.gpr .eax - 0#32 == 0#32) = _; rw [BitVec.sub_zero]; rfl)

theorem afterEncP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (EncodeDone g bs1 s ∧ SPreCtx g bs1 P L s) ∧ (EncodeDone g bs2 t ∧ SPreCtx g bs2 P L t))
      (afterEnc (privNameP v) (privCodeP v w) callArgsP) (fun _ _ => True) := by
  unfold afterEnc
  apply pair_seq_ct (cmp_relCT.mono (fun s t h => agree_regs (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.1.1.context.sp.trans h.2.1.context.sp.symm
    · exact encoded_status h.1.1 h.2.1)) (fun _ _ _ => trivial))
    (fun _ h => compareP_ready h) (fun _ h => compareP_ready h)
  apply RelCT.ite
  · intro s t h
    change s.zf = t.zf
    rw [h.1.1.flag, h.2.1.flag, encoded_status h.1.1.toEncodeDone h.2.1.toEncodeDone]
  · exact zeroOut_relCT.mono (fun _ _ h => ⟨h.1.1.1.context, h.1.2.1.context⟩) (fun _ _ _ => trivial)
  · exact (callThenWipeP_relCT v w nb eb).mono
      (fun _ _ h => ⟨⟨h.1.1.1.context, h.1.1.2⟩, ⟨h.1.2.1.context, h.1.2.2⟩⟩) (fun _ _ _ => trivial)

theorem encArgsP_ready {bs : Fin 8 → List Byte} {s : State} (h : Context g bs s ∧ SPreCtx g bs P L s) :
    WP isa (.block encArgs) s (fun t => EncodeReady g bs t ∧ SPreCtx g bs P L t) := by
  refine WP.mono (encArgs_ok h.1) ?_
  rintro t ⟨ht, M, K, dst, len, hash, src, count⟩
  exact ⟨⟨ht, dst, len, hash, src, count⟩, h.2.after (by rw [M]; exact Frame.refl _ _) K⟩

theorem encodeP_done {bs : Fin 8 → List Byte} {s : State} (h : EncodeReady g bs s ∧ SPreCtx g bs P L s) :
    WP isa VG.Impl.RsaPkcs1Sig.X86.encode s (fun t => EncodeDone g bs t ∧ SPreCtx g bs P L t) := by
  refine WP.mono (encoding_ok h.1.context h.1.dst h.1.len h.1.hash h.1.src h.1.count) ?_
  rintro t ⟨ht, F, K, enc⟩
  exact ⟨⟨ht, enc⟩, h.2.after (F.sub (by
    intro r hr; obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, by simp [bodyWrites], fun _ hx => hx⟩)) K⟩

theorem bodyP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (Context g bs1 s ∧ SPreCtx g bs1 P L s) ∧ (Context g bs2 t ∧ SPreCtx g bs2 P L t))
      (body (privNameP v) (privCodeP v w) callArgsP) (fun _ _ => True) := by
  unfold body
  apply pair_seq_ct (encArgs_relCT.mono
    (fun _ _ h => sp_agree (h.1.1.sp.trans h.2.1.sp.symm)) (fun _ _ _ => trivial))
    (fun _ h => encArgsP_ready h) (fun _ h => encArgsP_ready h)
  exact pair_seq_ct (encode_relCT.mono (fun _ _ h => encodeReady_agree h.1.1 h.2.1) (fun _ _ _ => trivial))
    (fun _ h => encodeP_done h) (fun _ h => encodeP_done h) (afterEncP_relCT v w nb eb)

theorem allocationP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun a b => ∃ s t, (FnInput g bs1 s ∧ SPreCtx g bs1 P L (entered s)) ∧
      (FnInput g bs2 t ∧ SPreCtx g bs2 P L (entered t)) ∧
      a = pushed savedRegisters s ∧ b = pushed savedRegisters t)
      (.frame (.alloc VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes)
        (body (privNameP v) (privCodeP v w) callArgsP) (.free VG.Impl.RsaPkcs1Sig.X86.Sign.frameBytes))
      (fun a b => a.gpr .esp = b.gpr .esp) := by
  intro a b ta tb a' b' hp ea eb'
  obtain ⟨s, t, ⟨hs, Hs⟩, ⟨ht, Ht⟩, rfl, rfl⟩ := hp
  have sp : (pushed savedRegisters s).gpr .esp = (pushed savedRegisters t).gpr .esp := by
    rw [hs.savedSp, ht.savedSp]
  have post : a'.gpr .esp = b'.gpr .esp := by
    rw [Exec.gpr (allocationP_noSp v w) ea, Exec.gpr (allocationP_noSp v w) eb', sp]
  cases ea with
  | frame pa ba _ =>
    cases eb' with
    | frame pb bb _ =>
      have ha := allocation_state pa
      have hb := allocation_state pb
      subst ha hb
      have eq := (bodyP_relCT v w nb eb) _ _ _ _ _ _ ⟨⟨hs.context, Hs⟩, ⟨ht.context, Ht⟩⟩ ba bb
      refine ⟨?_, post⟩
      rw [eq.1]
      rfl

theorem signFnP_relCT (v : CrtImpl) (w : CrtPImpl) {bs1 bs2 : Fin 8 → List Byte}
    (nb : bs1 0 = bs2 0) (eb : bs1 1 = bs2 1) :
    RelCT isa (fun s t => (FnInput g bs1 s ∧ SPreCtx g bs1 P L (entered s)) ∧
      (FnInput g bs2 t ∧ SPreCtx g bs2 P L (entered t)))
      (code (privNameP v) (privCodeP v w) callArgsP) (fun _ _ => True) := by
  unfold code
  refine RelCT.frame (R := fun _ _ => True) ?_ ?_
  · intro s t h
    have eq := h.1.1.savedSp.trans h.2.1.savedSp.symm
    rw [pushed_esp, pushed_esp] at eq
    have same := congrArg (fun x => x + BitVec.ofNat 32 (4 * savedRegisters.length)) eq
    simpa only [BitVec.sub_add_cancel] using same
  · refine VG.RelCT.seq ((allocationP_relCT v w (g := g) (P := P) (L := L) nb eb).mono ?_ (fun _ _ h => h))
      (restore_relCT.mono (fun _ _ h => sp_agree h) (fun _ _ _ => trivial))
    rintro a b ⟨s, t, h, rfl, rfl⟩
    exact ⟨s, t, h.1, h.2, rfl, rfl⟩
end

/-! ## The contract's public arguments -/

theorem argumentsP {s t : State} (H : (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pub s t) :
    s.gpr .esp = t.gpr .esp ∧ ∀ i < 23, arg s i = arg t i := by
  sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes] at H
  sig_split H
  constructor
  · assumption
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
        i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨
        i = 22 := by
      omega_using [hi]
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem publicBytesP {s t : State} (H : (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pub s t) :
    signBytes s 0 = signBytes t 0 ∧ signBytes s 1 = signBytes t 1 := by
  have Args := argumentsP H
  have Leak : ((signBytes s 0) ++ (signBytes s 1)).map (·.toNat) =
      ((signBytes t 0) ++ (signBytes t 1)).map (·.toNat) := by
    sig_pub [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
      Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes] at H
    have L := H.2.1
    rw [List.map_append, List.map_append] at L
    have len : ((Spec.Rsa.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat).map (·.toNat) ++
        (Spec.Rsa.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat).map (·.toNat)).length =
        ((Spec.Rsa.bytesAt t.mem ((arg t 2).setWidth 64) (arg t 3).toNat).map (·.toNat) ++
        (Spec.Rsa.bytesAt t.mem ((arg t 4).setWidth 64) (arg t 5).toNat).map (·.toNat)).length := by
      simp only [List.length_append, List.length_map, Spec.Rsa.bytesAt, List.length_range,
        Args.2 3 (by decide), Args.2 5 (by decide)]
    simpa only [List.map_append, signBytes, signGeometry, Geometry.sourceLength,
      Fin.val_zero, Fin.val_one, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceLT, ite_true,
      VG.Proof.Bignum.X86.byteAddr] using List.append_inj_left L len
  have both := (List.map_inj_right (fun x y h => BitVec.eq_of_toNat_eq h)).mp Leak
  have sameLength : (signBytes s 0).length = (signBytes t 0).length := by
    simp only [signBytes, Spec.Rsa.bytesAt, List.length_map, List.length_range]
    change (arg s 3).toNat = (arg t 3).toNat
    rw [Args.2 3 (by decide)]
  exact ⟨List.append_inj_left both sameLength, List.append_inj_right both sameLength⟩

theorem publicGeometryP {s t : State} (H : (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pub s t) :
    signGeometry s = signGeometry t := by
  obtain ⟨sp, args⟩ := argumentsP H
  have sources : (fun i : Fin 8 => arg s (if i.val < 2 then 2 + 2 * i.val else if i.val = 2 then 7 else 3 + 2 * i.val)) =
      (fun i : Fin 8 => arg t (if i.val < 2 then 2 + 2 * i.val else if i.val = 2 then 7 else 3 + 2 * i.val)) := by
    funext i
    apply args
    split
    · omega_using []
    · split <;> omega_using []
  simp only [signGeometry, sp, sources, args 0 (by decide), args 19 (by decide),
    args 3 (by decide), args 5 (by decide), args 10 (by decide), args 12 (by decide), args 20 (by decide),
    args 6 (by decide), args 8 (by decide)]

theorem sign_contractP_ct (v : CrtImpl) (w : CrtPImpl) :
    ConstantTime isa (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pub (code (privNameP v) (privCodeP v w) callArgsP) := by
  intro s t tr1 tr2 u u' hs ht hp e1 e2
  obtain ⟨Is, Hs⟩ := sign_contractP_pre hs
  obtain ⟨It, Ht⟩ := sign_contractP_pre ht
  obtain ⟨nb, eb⟩ := publicBytesP hp
  have geometry := publicGeometryP hp
  rw [← geometry] at It Ht
  rw [← (argumentsP hp).2 21 (by decide), ← (argumentsP hp).2 22 (by decide)] at Ht
  exact (signFnP_relCT v w nb eb s t tr1 tr2 u u' ⟨⟨Is, Hs⟩, ⟨It, Ht⟩⟩ e1 e2).1

/-! ## A state that meets the contract -/

open VG.Proof.Rsa.PreKey (keyIn keyMem key_pre_of)

/-- The arguments of `preState`: `out` at `0x1000`, the key (`keyMem`: `n`
at `0x2000`, `p` at `0x4200`, `q` at `0x4300`, `pre` at `0x4800`), `e` at
`0x3000`, `digest` at `0x4000`, `dp`, `dq` and `qinv` at `0x4400`, `0x4500`
and `0x4600`, `scratch` at `0xA000`. -/
def preArgs : List Nat := [0x1000, 64, 0x2000, 64, 0x3000, 1, 0, 0x4000, 64, 0x4200, 32, 0x4300, 32, 0x4400, 32, 0x4500, 32, 0x4600, 32, 0xa000, 0x420, 0x4800, 24]

/-- The memory of `preState`: the arguments on the stack from `0x20004`,
and the key. -/
def preMem (a : Addr) : Byte :=
  let i := a.toNat
  bif Nat.ble 0x20004 i && Nat.blt i 0x20060 then
    BitVec.ofNat 8 (preArgs.getD ((i - 0x20004) / 4) 0 / 256 ^ ((i - 0x20004) % 4))
  else bif keyIn i then keyMem a else 0

def preState : State where
  gpr r := if r = .esp then 0x20000 else 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := preMem
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x4200, 32⟩, ⟨0x4300, 32⟩, ⟨0x4400, 32⟩,
    ⟨0x4500, 32⟩, ⟨0x4600, 32⟩, ⟨0x4800, 192⟩]
  wr := [⟨0x1000, 64⟩, ⟨0xA000, 8448⟩, ⟨0x20004, 92⟩]

theorem preState_key : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt preState.mem 0x2000 64)
    (Spec.Rsa.bytesAt preState.mem 0x4200 32) (Spec.Rsa.bytesAt preState.mem 0x4300 32) =
      some (Spec.Rsa.wordsAt preState.mem 0x4800 24) :=
  key_pre_of fun a ha => by
    have hs : (Nat.ble 0x20004 a.toNat && Nat.blt a.toNat 0x20060) = false := by
      simp only [keyIn, Bool.or_eq_true, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at ha
      refine Bool.eq_false_iff.mpr fun h => ?_
      simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
      omega
    show (bif _ then _ else _) = _
    rw [hs, Bool.cond_false, ha, Bool.cond_true]

theorem satisfiablePre : ∃ s, (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack).pre s := by
  have a2 : arg preState 2 = 0x2000 := by decide
  have a3 : arg preState 3 = 64 := by decide
  have a9 : arg preState 9 = 0x4200 := by decide
  have a10 : arg preState 10 = 32 := by decide
  have a11 : arg preState 11 = 0x4300 := by decide
  have a12 : arg preState 12 = 32 := by decide
  have a21 : arg preState 21 = 0x4800 := by decide
  have a22 : arg preState 22 = 24 := by decide
  have e : argAddr preState 0 = 0x20004 := by decide
  have esp : preState.gpr .esp = 0x20000 := rfl
  have p2 : BitVec.setWidth 64 (arg preState 2) = 0x2000 := by rw [a2]; decide
  have p9 : BitVec.setWidth 64 (arg preState 9) = 0x4200 := by rw [a9]; decide
  have p11 : BitVec.setWidth 64 (arg preState 11) = 0x4300 := by rw [a11]; decide
  have p21 : BitVec.setWidth 64 (arg preState 21) = 0x4800 := by rw [a21]; decide
  have l3 : (arg preState 3).toNat = 64 := by rw [a3]; decide
  have l10 : (arg preState 10).toNat = 32 := by rw [a10]; decide
  have l12 : (arg preState 12).toNat = 32 := by rw [a12]; decide
  have l22 : (arg preState 22).toNat = 24 := by rw [a22]; decide
  refine ⟨preState, ?_⟩
  sig_pre [Spec.RsaPkcs1Sig.signPrecomputedContract, Spec.RsaPkcs1Sig.signPrecomputedSig,
    Spec.RsaPkcs1Sig.signSig, abi, argSlots, argVal, argBytes, stackBelow, e, esp,
    sigStack, Spec.Rsa.lenValid, Spec.Rsa.scratchWords, Spec.Rsa.privatePrecomputedWords]
  sig_and_intros
  rotate_right
  · rw [p2, p9, p11, p21, l3, l10, l12, l22]; exact preState_key
  all_goals first
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (intro a h₁ h₂
       sig_simp_only [Region.Contains, preState] at h₁ h₂
       bv_omega)

/-- `vg_rsa_pkcs1_sign_precomputed`, calling `vg_rsa_private_checked_precomputed` (with
`vg_rsa_private_crt_precomputed`). -/
theorem signPrecomputed_verified (v : CrtImpl) :
    Verified target (code (privNameP v) (privCodeP v crtPBaseline) callArgsP)
      (Spec.RsaPkcs1Sig.signPrecomputedContract abi sigStack) :=
  ⟨sign_contractP_correct v crtPBaseline, sign_contractP_ct v crtPBaseline, satisfiablePre⟩
end VG.Proof.RsaPkcs1Sig.X86.Sgn
