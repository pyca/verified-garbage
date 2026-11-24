module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.DecP
import VerifiedGarbage.Proof.Rsa.PreKey
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratchArgs
public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Wp
public import VerifiedGarbage.Proof.Framework.PPC64LE.CallAny
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Rsa.BytesFrame
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
public import VerifiedGarbage.Proof.RsaPss.PPC64LE.ShiftV
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Dc.Shift
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Encode
import VerifiedGarbage.Proof.Mgf1.Bytes
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Impl.RsaPkcs1Enc.PPC64LE.Front
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.RsaPkcs1Enc.Contract

/-!
# `vg_rsa_pkcs1_decrypt_precomputed_front` on PPC64LE

`Front.code` (`Impl/RsaPkcs1Enc/PPC64LE/Front.lean`) against
`Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract` with 3920 bytes of stack
(`front_verified`), for any callee verified against
`Proof.RsaPkcs1Enc.decryptPrecomputedContract` with 3648 (`K`) whose frames
use at most 3648 bytes (`sdepth`): its proof is used only through that
contract.

**The precondition.** `fpre_of` names the facts of ours: those of the
callee's (`Dec.DPre true`, `Dec.PreX`) and that the 3920 bytes of stack below
the stack pointer (`bigR`) are apart from the buffers and the stack
arguments (`Big`).

**The call.** `setup` (`setup_ok`) copies our 17 stack arguments to the
frame's Parameter Save Area, saves `r14`–`r17` and the return address in
the slots above them (`Slots`), and leaves `out`, `k`, `msg_len` and
`scratch` in `r14`–`r17` (`Set`). The callee's entry (`entry`) has our
argument registers, the copies as its stack arguments and our buffers as
its regions, apart from the frame and below it (`dpre_entry`,
`prex_entry`), so its contract holds there (`dec_pre_of`); its
postcondition (`dec_post`) is of our arguments, since the frame is apart
from the buffers it reads (`decOf_entry`), and the callee writes only the
buffers and the stack below the frame, not the slots (`call_ok`,
`Called`).

**After the call.** The tail (`Mid`): the buffer, the first 2048 bytes of
`scratch`, cleared (`clear_ok`), `out` copied to it (`copyIn_ok`), shifted
left by `k - L` in eleven passes (`pass_ok`, `shift_ok`: RSASSA-PSS's
`shV`, here with eleven passes, `shV_in11`), and its first `k` bytes copied
back to `out` (`copyOut_ok`), which leaves the message first (`shape`,
`shifted`); `restore_ok` restores `r14`–`r17` (`front_ok`).

**Constant time.** Two runs related by the contract's public data
(`front_pub`): the blocks by the taint analysis, from the stack pointer or
from `r14`–`r17` (`setup_taint`, `after_taint`, `tail_taint`,
`restore_taint`), the call by the callee's constant time, its public data
(`dec_pub_of`) being ours (`leak_entry`) (`front_ct`).
-/

-- separate module: the function's proofs, apart from the cleanup's framework, whose `PPC64LE.frameBytes` would shadow the frame's size

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.PPC64LE.Front

open VG VG.PPC64LE
open VG.Proof.RsaPkcs1Enc.PPC64LE.Dec (DPre PreX stackBytes oR mlR nR eR dR iR pR qR dpR dqR qiR sR aR preR kR rdL
  fnPost stackArgs_seventeen)

/-! ## The contracts -/

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s contract, with the stack its code uses. -/
abbrev K : Contract isa := Proof.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes

/-- The stack the function uses: its frame and the callee's. -/
def fStack : Nat := 3920

/-- Its contract. -/
abbrev FK : Contract isa := Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi fStack

/-- The stack the function and its callee use. -/
abbrev bigR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 fStack, fStack⟩

/-- What the function's precondition says of the stack it uses. -/
structure Big (s : State) : Prop where
  sp : fStack ≤ s.sp.toNat
  ko : (bigR s).Disjoint (oR s)
  km : (bigR s).Disjoint (mlR s)
  kn : (bigR s).Disjoint (nR s)
  ke : (bigR s).Disjoint (eR s)
  kd : (bigR s).Disjoint (dR s)
  ki : (bigR s).Disjoint (iR s)
  kp : (bigR s).Disjoint (pR s)
  kq : (bigR s).Disjoint (qR s)
  kdp : (bigR s).Disjoint (dpR s)
  kdq : (bigR s).Disjoint (dqR s)
  kqi : (bigR s).Disjoint (qiR s)
  ks : (bigR s).Disjoint (sR s)
  kP : (bigR s).Disjoint (preR s)
  ka : (bigR s).Disjoint (aR true s)

theorem kR_sub (s : State) (h : fStack ≤ s.sp.toNat) : Region.Sub (kR s) (bigR s) :=
  below_sub (by decide) (by unfold fStack at *; omega_using [h])

theorem fpre_of {s : State} (h : FK.pre s) : DPre true s ∧ PreX s ∧ Big s := by
  have e : fStack = 3919 + 1 := rfl
  change (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi fStack).pre s at h
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
    abi, argRegs, stackArgs_seventeen, List.append_eq] at h
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil] at h
  sig_split h
  rename_i sp1 sp2 hrd hwr om on hio ko km kn ke kd ki kp kq kdp kdq kqi ks kP ka wo wm wn we wd wi wp wq wdp wdq
    wqi ws wP h_k1_k2 h4 hi e1 e2 d1 d2 p1 p2 q1 q2 h8 h12 h10 hs hpl
  have hyp := h
  sig_split hio
  rename_i oe od oi op oq odp odq oqi os oP oa mn me md mi mp mq mdp mdq mqi ms mP ma ns es ds is ps qs dps dqs
    qis sP
  have sa := hio
  obtain ⟨k1, k2⟩ := h_k1_k2
  have big : Big s := ⟨by rw [e]; exact sp1, ko, km, kn, ke, kd, ki, kp, kq, kdp, kdq, kqi, ks, kP, ka⟩
  have sub := kR_sub s big.sp
  have s1 : stackBytes ≤ s.sp.toNat := by
    have := big.sp
    unfold stackBytes Impl.RsaPkcs1Enc.PPC64LE.Decrypt.frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes
    unfold fStack at this; omega_using [this]
  exact ⟨⟨s1,
    by simp only [↓reduceIte]; omega_using [sp2], hrd, hwr, om, on, oe, od, oi, op, oq, odp, odq, oqi, os, oa, mn,
    me, md, mi, mp, mq, mdp, mdq, mqi, ms, ma, ns, es, ds, is, ps, qs, dps, dqs, qis, sa, ko.sub_left sub,
    km.sub_left sub, kn.sub_left sub, ke.sub_left sub, kd.sub_left sub, ki.sub_left sub, kp.sub_left sub,
    kq.sub_left sub, kdp.sub_left sub, kdq.sub_left sub, kqi.sub_left sub, ks.sub_left sub, ka.sub_left sub, wo, wm,
    wn, we, wd, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h4, hi, e1, e2, d1, d2, p1, p2, q1, q2, h8, h12, h10, hs⟩,
    ⟨oP, mP, sP, kP.sub_left sub, wP, hpl, fun _ => hyp⟩, big⟩

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s precondition, from its facts. -/
theorem dec_pre_of {s : State} (h : DPre true s) (x : PreX s) : K.pre s := by
  have e : stackBytes = 3647 + 1 := rfl
  have sp1 := h.sp1
  show (Proof.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pre s
  rw [e] at sp1 ⊢
  sig_pre [Proof.RsaPkcs1Enc.decryptPrecomputedContract, Proof.RsaPkcs1Enc.decryptPrecomputedSig,
    Proof.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq]
  simp only [Sig.pairFacts, List.filterMap_cons, List.filterMap_nil, Bool.cond_true, Bool.cond_false,
    Bool.true_or, Bool.false_or, List.cons_append, List.nil_append, Sig.conj, List.append_nil]
  exact ⟨sp1, by have := h.sp2; simp only [↓reduceIte] at this; omega_using [this], h.hrd, h.hwr, h.om, h.on,
    ⟨h.oe, h.od, h.oi, h.op, h.oq, h.odp, h.odq, h.oqi, h.os, x.oP, h.oa, h.mn, h.me, h.md, h.mi, h.mp, h.mq, h.mdp,
      h.mdq, h.mqi, h.ms, x.mP, h.ma, h.ns, h.es, h.ds, h.is, h.ps, h.qs, h.dps, h.dqs, h.qis, x.sP, h.sa⟩,
    h.ko, h.km, h.kn, h.ke, h.kd, h.ki, h.kp, h.kq, h.kdp, h.kdq, h.kqi, h.ks, x.kP, h.ka, h.wo, h.wm, h.wn, h.we,
    h.wd, h.wi, h.wp, h.wq, h.wdp, h.wdq, h.wqi, h.ws, x.wP, ⟨h.k1, h.k2⟩, h.h4, h.hi, h.e1, h.e2, h.d1, h.d2, h.p1,
    h.p2, h.q1, h.q2, h.h8, h.h12, h.h10, h.hs, x.pl, x.hyp rfl⟩

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s postcondition, on the registers. -/
theorem dec_post {s s' : State} (h : K.post s s') : fnPost s s' := by
  have e : stackBytes = 3647 + 1 := rfl
  change (Proof.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).post s s' at h
  rw [e] at h
  sig_post [Proof.RsaPkcs1Enc.decryptPrecomputedContract, Proof.RsaPkcs1Enc.decryptPrecomputedSig,
    Proof.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq] at h
  exact h

/-! ## The frame -/

open VG.Impl.RsaPkcs1Enc.PPC64LE.Front (frameBytes o14 o15 o16 o17 oLr)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only Keep MemTo wp_nil wp_li wp_addi wp_subi wp_add wp_sub wp_and wp_xor wp_lsr
  wp_mov wp_addSp wp_mflr wp_mtlr wp_lbz wp_ld wp_stb wp_std)

/-- The frame's base. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The base of the stack the function and its callee use. -/
abbrev kb (s : State) : Addr := s.sp - BitVec.ofNat 64 fStack

theorem fb_eq (s : State) : fb s = kb s + BitVec.ofNat 64 3648 := Offset.sub_ofNat_eq _ (by decide)

/-- A part of the frame is in the stack the function uses. -/
theorem fslot_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (bigR s) := by
  rw [fb_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact Offset.sub_base _ (by unfold fStack frameBytes at *; omega_using [h])

/-- The stack the callee uses, below the frame. -/
abbrev kF (s : State) : Region := ⟨fb s - BitVec.ofNat 64 3648, 3648⟩

theorem kF_eq (s : State) : kF s = ⟨kb s, 3648⟩ := by
  simp only [kF, fb_eq, BitVec.add_sub_cancel]

theorem kF_sub (s : State) : Region.Sub (kF s) (bigR s) := by
  rw [kF_eq]; exact Region.sub_prefix (by decide)

/-- The copies of the stack arguments, which the callee reads. -/
abbrev aF (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 136⟩

/-- The copies and the slots. -/
abbrev slR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 96, 176⟩

theorem fb_toNat {s : State} (h : Big s) : (kb s).toNat + fStack = s.sp.toNat := by
  have := h.sp
  simp only [kb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold fStack at *; omega_using [this]

/-- What `setup` leaves in the frame. -/
structure Slots (s : State) (m : Mem) : Prop where
  copy : ∀ j < 17, m.readW (fb s + BitVec.ofNat 64 (96 + 8 * j)) 64 = stackArg s j
  s14 : m.readW (fb s + BitVec.ofNat 64 232) 64 = s.gpr .r14
  s15 : m.readW (fb s + BitVec.ofNat 64 240) 64 = s.gpr .r15
  s16 : m.readW (fb s + BitVec.ofNat 64 248) 64 = s.gpr .r16
  s17 : m.readW (fb s + BitVec.ofNat 64 256) 64 = s.gpr .r17
  slr : m.readW (fb s + BitVec.ofNat 64 264) 64 = s.lr

theorem slot_in (s : State) {d : Nat} (h₁ : 96 ≤ d) (h₂ : d + 8 ≤ 272) : (slR s).Contains (fb s + BitVec.ofNat 64 d) 8 :=
  Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])

/-- The slots, after writes apart from them. -/
theorem Slots.frame {s : State} {m m' : Mem} {rs : List Region} (h : Slots s m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (slR s).Disjoint r) : Slots s m' := by
  have e : ∀ {d : Nat}, 96 ≤ d → d + 8 ≤ 272 → m'.readW (fb s + BitVec.ofNat 64 d) 64 = m.readW (fb s + BitVec.ofNat 64 d) 64 :=
    fun h₁ h₂ => hf.readW (slot_in s h₁ h₂) hd (by decide)
  exact ⟨fun j hj => (e (by omega_using []) (by omega_using [hj])).trans (h.copy j hj),
    (e (by decide) (by decide)).trans h.s14, (e (by decide) (by decide)).trans h.s15,
    (e (by decide) (by decide)).trans h.s16, (e (by decide) (by decide)).trans h.s17,
    (e (by decide) (by decide)).trans h.slr⟩

/-- The registers `setup` writes. -/
abbrev setRegs : List Reg := [.r0, .r12, .r14, .r15, .r16, .r17]

/-- The state after `setup`. -/
structure Set (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr
  lr : t.lr = s.lr
  g : ∀ r, r ∉ setRegs → t.gpr r = s.gpr r
  g14 : t.gpr .r14 = s.gpr .r3
  g15 : t.gpr .r15 = s.gpr .r4
  g16 : t.gpr .r16 = s.gpr .r5
  g17 : t.gpr .r17 = stackArg s 13
  fr : Frame [⟨fb s, 272⟩] s.mem t.mem
  sl : Slots s t.mem

theorem wp_of_exec {is : List Instr} {s s' : State} {t : List Leak} {Q : State → Prop}
    (h : execBlock isa is s = some (s', t)) (hq : Q s') : WP isa (.block is) s Q := ⟨t, s', .block h, hq⟩

theorem frame_in (s : State) {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 272) :
    InRegions (⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr) (fb s + BitVec.ofNat 64 d) 8 :=
  ⟨_, List.mem_cons_self .., Offset.contains _ h₁ (by omega_using [h₂]) (by omega_using [])⟩

/-- The caller's stack arguments, from the frame's base. -/
theorem argAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = fb s + BitVec.ofNat 64 (frameBytes + 96 + 8 * j) := by
  rw [← Offset.add_add_eq (fb s) (a := frameBytes) (b := 32 + 8 * (8 + j)) (c := frameBytes + 96 + 8 * j)
    (by unfold frameBytes; omega_using []), fb, BitVec.sub_add_cancel]
  rfl

/-- The caller's stack arguments are readable. -/
theorem arg_in {s : State} (hp : DPre true s) {j : Nat} (hj : j < 17) {X : List Region} :
    InRegions (s.rd ++ X) (stackArgAddr s j) 8 := by
  refine ⟨aR true s, List.mem_append_left _ (by rw [hp.hrd]; simp), ?_⟩
  simp only [aR, ↓reduceIte, stackArgAddr]
  rw [show 32 + 8 * (8 + j) = 96 + 8 * j by omega_using []]
  have := hp.sp2
  simp only [↓reduceIte] at this
  rw [show s.sp + BitVec.ofNat 64 (96 + 8 * j) = s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 (8 * j) by
    rw [Offset.add_add]]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

/-- `setup`, from the frame's allocation. -/
theorem setup_ok {s : State} (hp : DPre true s) (big : Big s) :
    WP isa (.block Impl.RsaPkcs1Enc.PPC64LE.Front.setup) (allocated frameBytes s) (Set s) := by
  have hK := fb_toNat big
  have sp2 := hp.sp2
  simp only [↓reduceIte] at sp2
  have hF : (fb s).toNat + 272 = s.sp.toNat := by
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes; unfold fStack at hK; omega_using [hK]
  let a := allocated frameBytes s
  have asp : a.sp = fb s := rfl
  have awr : a.wr = ⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr := rfl
  have ard : a.rd = s.rd := rfl
  have amem : a.mem = s.mem.write (fb s) 8 s.sp := rfl
  rw [Impl.RsaPkcs1Enc.PPC64LE.Front.setup, List.append_assoc, List.singleton_append]
  refine wp_addSp fun u o₀ e₀ => ?_
  rw [WP.block_append_iff]
  have u12 : u.gpr .r12 = u.sp := by rw [e₀, o₀.sp, BitVec.add_zero]
  have usp : u.sp = fb s := o₀.sp
  -- The caller's stack arguments, readable.
  have hsrc : ∀ j < 17, InRegions (u.rd ++ u.wr) (u.sp + BitVec.ofNat 64 (frameBytes + 96 + 8 * j)) 8 := by
    intro j hj
    rw [usp, ← argAddr_eq, o₀.rd, o₀.wr]
    refine ⟨aR true s, List.mem_append_left _ (by show aR true s ∈ s.rd; rw [hp.hrd]; simp), ?_⟩
    simp only [aR, ↓reduceIte, stackArgAddr]
    rw [show 32 + 8 * (8 + j) = 96 + 8 * j by omega_using []]
    exact Offset.contains _ (d := 96 + 8 * j) (e := 96) (by omega_using []) (by omega_using [hj])
      (by omega_using [])
  have hdst : ∀ j < 17, InRegions u.wr (u.sp + BitVec.ofNat 64 (96 + 8 * j)) 8 := fun j hj => by
    rw [usp, o₀.wr]; exact frame_in s (by omega_using []) (by omega_using [hj])
  refine wp_of_exec (copies_run u12 (by decide) 17 (by decide) hsrc hdst) ?_
  obtain ⟨fc, vc⟩ := copiedState_mem (bytes := frameBytes) (u := u) 17 (by decide) (by decide)
  generalize hc : copiedState frameBytes u 17 = c at fc vc ⊢
  have csp : c.sp = fb s := by rw [← hc, copiedState_sp, usp]
  have crd : c.rd = s.rd := by rw [← hc, copiedState_rd, o₀.rd]; rfl
  have cwr : c.wr = ⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr := by rw [← hc, copiedState_wr, o₀.wr]; rfl
  have clr : c.lr = s.lr := by rw [← hc, copiedState_lr, o₀.lr]; rfl
  have cg : ∀ r, r ≠ .r0 → r ≠ .r12 → c.gpr r = s.gpr r := fun r h0 h12 => by
    rw [← hc, copiedState_gpr _ _ h0, o₀.gpr r (by simpa using h12)]; rfl
  have c12 : c.gpr .r12 = fb s := by rw [← hc, copiedState_gpr _ _ (by decide), u12, usp]
  have cw : ∀ {d : Nat}, 32 ≤ d → d + 8 ≤ 272 → InRegions c.wr (c.gpr .r12 + BitVec.ofNat 64 d) 8 :=
    fun h₁ h₂ => by rw [cwr, c12]; exact frame_in s h₁ h₂
  refine wp_std rfl (cw (d := o14) (by decide) (by decide)) fun c₁ m₁ => ?_
  refine wp_std rfl (by rw [m₁.wr, m₁.gpr]; exact cw (d := o15) (by decide) (by decide)) fun c₂ m₂ => ?_
  refine wp_std rfl (by rw [m₂.wr, m₂.gpr, m₁.wr, m₁.gpr]; exact cw (d := o16) (by decide) (by decide))
    fun c₃ m₃ => ?_
  refine wp_std rfl (by rw [m₃.wr, m₃.gpr, m₂.wr, m₂.gpr, m₁.wr, m₁.gpr]; exact cw (d := o17) (by decide) (by decide))
    fun c₄ m₄ => ?_
  refine wp_mflr fun c₅ o₅ e₅ => ?_
  have w6 : InRegions c₅.wr (c₅.gpr .r12 + BitVec.ofNat 64 oLr) 8 := by
    rw [o₅.wr, m₄.wr, o₅.get .r12, m₄.gpr, m₃.wr, m₃.gpr, m₂.wr, m₂.gpr, m₁.wr, m₁.gpr]
    exact cw (by decide) (by decide)
  refine wp_std rfl w6 fun c₆ m₆ => ?_
  refine wp_mov fun c₇ o₇ e₇ => wp_mov fun c₈ o₈ e₈ => wp_mov fun c₉ o₉ e₉ => ?_
  have g12 : c₉.gpr .r12 = fb s := by
    rw [o₉.get .r12, o₈.get .r12, o₇.get .r12, m₆.gpr, o₅.get .r12, m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr, c12]
  have hrd9 : c₉.rd = s.rd := by rw [o₉.rd, o₈.rd, o₇.rd, m₆.rd, o₅.rd, m₄.rd, m₃.rd, m₂.rd, m₁.rd, crd]
  have hwr9 : c₉.wr = ⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr := by
    rw [o₉.wr, o₈.wr, o₇.wr, m₆.wr, o₅.wr, m₄.wr, m₃.wr, m₂.wr, m₁.wr, cwr]
  refine wp_ld rfl (by rw [g12, hrd9, ← argAddr_eq]; exact arg_in hp (by decide)) fun c₁₀ o₁₀ e₁₀ => wp_nil ?_
  have rlr : c₄.lr = s.lr := by rw [m₄.lr, m₃.lr, m₂.lr, m₁.lr, clr]
  -- The memory, by name.
  have hm : c₁₀.mem = ((((c.mem.writeW (fb s + BitVec.ofNat 64 o14) (c.gpr .r14)).writeW
      (fb s + BitVec.ofNat 64 o15) (c.gpr .r15)).writeW (fb s + BitVec.ofNat 64 o16) (c.gpr .r16)).writeW
      (fb s + BitVec.ofNat 64 o17) (c.gpr .r17)).writeW (fb s + BitVec.ofNat 64 oLr) c₄.lr := by
    rw [o₁₀.mem, o₉.mem, o₈.mem, o₇.mem, m₆.mem, o₅.mem, m₄.mem, m₃.mem, m₂.mem, m₁.mem, e₅, o₅.get .r12,
      m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr, c12]
  rw [rlr, cg _ (by decide) (by decide), cg _ (by decide) (by decide), cg _ (by decide) (by decide),
    cg _ (by decide) (by decide)] at hm
  unfold o14 o15 o16 o17 oLr at hm
  -- `s`'s memory outside the frame, and the copies.
  have fa : Frame [⟨fb s, 272⟩] s.mem u.mem := by
    rw [o₀.mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self' (by decide))
  have fcs : Frame [⟨fb s, 272⟩] s.mem c.mem := fa.trans (Frame.sub fc fun r hr => by
    rw [List.mem_singleton.mp hr, usp]
    exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)
  have sepW : ∀ {d e : Nat} (m : Mem) (v : BitVec 64), d + 8 ≤ e ∨ e + 8 ≤ d → e + 8 ≤ 272 → d + 8 ≤ 2 ^ 32 →
      (m.writeW (fb s + BitVec.ofNat 64 e) v).readW (fb s + BitVec.ofNat 64 d) 64 =
        m.readW (fb s + BitVec.ofNat 64 d) 64 := fun m v h he hd =>
    Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hd]) (by omega_using [he])) (by decide)
  have outF : ∀ {d : Nat}, 272 ≤ d → d + 8 ≤ 2 ^ 32 →
      c.mem.readW (fb s + BitVec.ofNat 64 d) 64 = s.mem.readW (fb s + BitVec.ofNat 64 d) 64 := fun h₁ h₂ =>
    fcs.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ h₁ (by omega_using [h₂])) (by decide)
  have inF : ∀ {d : Nat}, d + 8 ≤ 272 → (⟨fb s, 272⟩ : Region).Contains (fb s + BitVec.ofNat 64 d) (64 / 8) :=
    fun h => Offset.contains_base _ (by omega_using [h]) (by omega_using [h])
  refine ⟨?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [o₁₀.sp, o₉.sp, o₈.sp, o₇.sp, m₆.sp, o₅.sp, m₄.sp, m₃.sp, m₂.sp, m₁.sp, csp]
  · rw [o₁₀.rd, hrd9]
  · rw [o₁₀.wr, hwr9]
  · rw [o₁₀.lr, o₉.lr, o₈.lr, o₇.lr, m₆.lr, o₅.lr, rlr]
  · simp only [setRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h12, h14, h15, h16, h17⟩ := hr
    rw [o₁₀.get r (by simpa using h17), o₉.get r (by simpa using h16), o₈.get r (by simpa using h15),
      o₇.get r (by simpa using h14), m₆.gpr, o₅.get r (by simpa using h0), m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr,
      cg r h0 h12]
  · rw [o₁₀.get .r14, o₉.get .r14, o₈.get .r14, e₇, m₆.gpr, o₅.get .r3, m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr,
      cg _ (by decide) (by decide)]
  · rw [o₁₀.get .r15, o₉.get .r15, e₈, o₇.get .r4, m₆.gpr, o₅.get .r4, m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr,
      cg _ (by decide) (by decide)]
  · rw [o₁₀.get .r16, e₉, o₈.get .r5, o₇.get .r5, m₆.gpr, o₅.get .r5, m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr,
      cg _ (by decide) (by decide)]
  · rw [e₁₀, g12, ← o₁₀.mem, hm, show frameBytes + 96 + 8 * 13 = 472 from rfl]
    rw [sepW _ _ (by decide) (by decide) (by decide), sepW _ _ (by decide) (by decide) (by decide),
      sepW _ _ (by decide) (by decide) (by decide), sepW _ _ (by decide) (by decide) (by decide),
      sepW _ _ (by decide) (by decide) (by decide), outF (by decide) (by decide),
      show (472 : Nat) = frameBytes + 96 + 8 * 13 from rfl, ← argAddr_eq]
    rfl
  · rw [hm]
    exact ((((fcs.writeW (List.mem_singleton_self _) _ (inF (by decide))).writeW (List.mem_singleton_self _) _
      (inF (by decide))).writeW (List.mem_singleton_self _) _ (inF (by decide))).writeW
      (List.mem_singleton_self _) _ (inF (by decide))).writeW (List.mem_singleton_self _) _ (inF (by decide))
  · rw [hm, sepW _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]),
      sepW _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]),
      sepW _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]),
      sepW _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]),
      sepW _ _ (by omega_using [hj]) (by decide) (by omega_using [hj]), ← usp, vc j hj, usp,
      fa.readW (Region.contains_self _ _) (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint_base _ (by unfold frameBytes; omega_using [])
          (by unfold frameBytes; omega_using [hj])) (by decide), ← argAddr_eq]
    rfl
  · rw [hm, sepW _ _ (by decide) (by decide) (by decide), sepW _ _ (by decide) (by decide) (by decide),
      sepW _ _ (by decide) (by decide) (by decide), sepW _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [hm, sepW _ _ (by decide) (by decide) (by decide), sepW _ _ (by decide) (by decide) (by decide),
      sepW _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [hm, sepW _ _ (by decide) (by decide) (by decide), sepW _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [hm, sepW _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [hm, Mem.readW_writeW_self64]

/-! ## The call -/

/-- The regions the callee reads: its buffers and the copies. -/
abbrev RD (s : State) : List Region := [nR s, eR s, dR s, iR s, pR s, qR s, dpR s, dqR s, qiR s, preR s, aF s]

/-- The regions the callee writes. -/
abbrev WR (s : State) : List Region := [oR s, mlR s, sR s]

theorem aF_sub (s : State) : Region.Sub (aF s) (bigR s) := fslot_sub s (by decide)

theorem kF_aF (s : State) : (kF s).Disjoint (aF s) := by
  rw [kF_eq]
  show (⟨kb s, 3648⟩ : Region).Disjoint ⟨fb s + BitVec.ofNat 64 96, 136⟩
  rw [fb_eq, Offset.add_add]
  exact Offset.base_disjoint _ (by decide) (by decide)

theorem stackBytes_eq : stackBytes = 3648 := rfl

/-- The callee's precondition's facts, in a state with our arguments, the
copies of the stack arguments at the frame's base and our regions. -/
theorem dpre_entry {s x : State} (hp : DPre true s) (big : Big s) (hsp : x.sp = fb s)
    (hg : ∀ r ∈ argRegs, x.gpr r = s.gpr r) (ha : ∀ j < 17, stackArg x j = stackArg s j)
    (hrd : x.rd = RD s) (hwr : x.wr = WR s) : DPre true x := by
  have hK := fb_toNat big
  have hF : (fb s).toNat + 272 = s.sp.toNat := by
    simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes; unfold fStack at hK; omega_using [hK]
  unfold fStack at hK
  have g3 := hg .r3 (by decide)
  have g4 := hg .r4 (by decide)
  have g5 := hg .r5 (by decide)
  have g6 := hg .r6 (by decide)
  have g7 := hg .r7 (by decide)
  have g8 := hg .r8 (by decide)
  have g9 := hg .r9 (by decide)
  have g10 := hg .r10 (by decide)
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have a6 := ha 6 (by decide)
  have a7 := ha 7 (by decide)
  have a8 := ha 8 (by decide)
  have a9 := ha 9 (by decide)
  have a10 := ha 10 (by decide)
  have a11 := ha 11 (by decide)
  have a12 := ha 12 (by decide)
  have a13 := ha 13 (by decide)
  have a14 := ha 14 (by decide)
  have a15 := ha 15 (by decide)
  have a16 := ha 16 (by decide)
  have eA : aR true x = aF s := by
    simp only [aR, ↓reduceIte, stackArgAddr, hsp]
  have eK : kR x = kF s := by simp only [kR, hsp, stackBytes_eq]
  exact {
    sp1 := by rw [hsp]; unfold stackBytes Impl.RsaPkcs1Enc.PPC64LE.Decrypt.frameBytes Impl.Rsa.PPC64LE.Priv.frameBytes; omega_using [hF, hK],
    sp2 := by rw [hsp]; simp only [↓reduceIte]; have := s.sp.isLt; omega_using [hF, this],
    hrd := by rw [hrd]; simp only [rdL, ↓reduceIte, eA, List.cons_append, List.nil_append, nR, eR, dR, iR, pR, qR, dpR,
      dqR, qiR, preR, g6, g7, g8, g9, g10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a15, a16],
    hwr := by rw [hwr]; simp only [oR, mlR, sR, g3, g4, g5, a13, a14],
    om := by simpa only [oR, g3, g4, mlR, g5] using hp.om,
    on := by simpa only [oR, g3, g4, nR, g6, g7] using hp.on,
    oe := by simpa only [oR, g3, g4, eR, g8, g9] using hp.oe,
    od := by simpa only [oR, g3, g4, dR, g10, a0] using hp.od,
    oi := by simpa only [oR, g3, g4, iR, a1, a2] using hp.oi,
    op := by simpa only [oR, g3, g4, pR, a3, a4] using hp.op,
    oq := by simpa only [oR, g3, g4, qR, a5, a6] using hp.oq,
    odp := by simpa only [oR, g3, g4, dpR, a7, a8] using hp.odp,
    odq := by simpa only [oR, g3, g4, dqR, a9, a10] using hp.odq,
    oqi := by simpa only [oR, g3, g4, qiR, a11, a12] using hp.oqi,
    os := by simpa only [oR, g3, g4, sR, a13, a14] using hp.os,
    mn := by simpa only [mlR, g5, nR, g6, g7] using hp.mn,
    me := by simpa only [mlR, g5, eR, g8, g9] using hp.me,
    md := by simpa only [mlR, g5, dR, g10, a0] using hp.md,
    mi := by simpa only [mlR, g5, iR, a1, a2] using hp.mi,
    mp := by simpa only [mlR, g5, pR, a3, a4] using hp.mp,
    mq := by simpa only [mlR, g5, qR, a5, a6] using hp.mq,
    mdp := by simpa only [mlR, g5, dpR, a7, a8] using hp.mdp,
    mdq := by simpa only [mlR, g5, dqR, a9, a10] using hp.mdq,
    mqi := by simpa only [mlR, g5, qiR, a11, a12] using hp.mqi,
    ms := by simpa only [mlR, g5, sR, a13, a14] using hp.ms,
    ns := by simpa only [nR, g6, g7, sR, a13, a14] using hp.ns,
    es := by simpa only [eR, g8, g9, sR, a13, a14] using hp.es,
    ds := by simpa only [dR, g10, a0, sR, a13, a14] using hp.ds,
    is := by simpa only [iR, a1, a2, sR, a13, a14] using hp.is,
    ps := by simpa only [pR, a3, a4, sR, a13, a14] using hp.ps,
    qs := by simpa only [qR, a5, a6, sR, a13, a14] using hp.qs,
    dps := by simpa only [dpR, a7, a8, sR, a13, a14] using hp.dps,
    dqs := by simpa only [dqR, a9, a10, sR, a13, a14] using hp.dqs,
    qis := by simpa only [qiR, a11, a12, sR, a13, a14] using hp.qis,
    wo := by simpa only [g3, g4] using hp.wo,
    wm := by simpa only [g5] using hp.wm,
    wn := by simpa only [g6, g7] using hp.wn,
    we := by simpa only [g8, g9] using hp.we,
    wd := by simpa only [g10, a0] using hp.wd,
    wi := by simpa only [a1, a2] using hp.wi,
    wp := by simpa only [a3, a4] using hp.wp,
    wq := by simpa only [a5, a6] using hp.wq,
    wdp := by simpa only [a7, a8] using hp.wdp,
    wdq := by simpa only [a9, a10] using hp.wdq,
    wqi := by simpa only [a11, a12] using hp.wqi,
    ws := by simpa only [a13, a14] using hp.ws,
    k1 := by simpa only [g7] using hp.k1,
    k2 := by simpa only [g7] using hp.k2,
    h4 := by simpa only [g4, g7] using hp.h4,
    hi := by simpa only [a2, g7] using hp.hi,
    e1 := by simpa only [g9] using hp.e1,
    e2 := by simpa only [g9, g7] using hp.e2,
    d1 := by simpa only [a0] using hp.d1,
    d2 := by simpa only [a0, g7] using hp.d2,
    p1 := by simpa only [a4] using hp.p1,
    p2 := by simpa only [a4, g7] using hp.p2,
    q1 := by simpa only [a6] using hp.q1,
    q2 := by simpa only [a6, g7] using hp.q2,
    h8 := by simpa only [a8, a4] using hp.h8,
    h12 := by simpa only [a12, a4] using hp.h12,
    h10 := by simpa only [a10, a6] using hp.h10,
    hs := by simpa only [g7, a14] using hp.hs,
    oa := by rw [eA]; simpa only [oR, g3, g4] using (big.ko.sub_left (aF_sub s)).symm,
    ma := by rw [eA]; simpa only [mlR, g5] using (big.km.sub_left (aF_sub s)).symm,
    sa := by rw [eA]; simpa only [sR, a13, a14] using (big.ks.sub_left (aF_sub s)).symm,
    ko := by rw [eK]; simpa only [oR, g3, g4] using big.ko.sub_left (kF_sub s),
    km := by rw [eK]; simpa only [mlR, g5] using big.km.sub_left (kF_sub s),
    kn := by rw [eK]; simpa only [nR, g6, g7] using big.kn.sub_left (kF_sub s),
    ke := by rw [eK]; simpa only [eR, g8, g9] using big.ke.sub_left (kF_sub s),
    kd := by rw [eK]; simpa only [dR, g10, a0] using big.kd.sub_left (kF_sub s),
    ki := by rw [eK]; simpa only [iR, a1, a2] using big.ki.sub_left (kF_sub s),
    kp := by rw [eK]; simpa only [pR, a3, a4] using big.kp.sub_left (kF_sub s),
    kq := by rw [eK]; simpa only [qR, a5, a6] using big.kq.sub_left (kF_sub s),
    kdp := by rw [eK]; simpa only [dpR, a7, a8] using big.kdp.sub_left (kF_sub s),
    kdq := by rw [eK]; simpa only [dqR, a9, a10] using big.kdq.sub_left (kF_sub s),
    kqi := by rw [eK]; simpa only [qiR, a11, a12] using big.kqi.sub_left (kF_sub s),
    ks := by rw [eK]; simpa only [sR, a13, a14] using big.ks.sub_left (kF_sub s),
    ka := by rw [eK, eA]; exact kF_aF s }

theorem frame_big (s : State) : Region.Sub ⟨fb s, 272⟩ (bigR s) := by
  have := fslot_sub s (d := 0) (n := 272) (by decide)
  rwa [BitVec.add_zero] at this

/-- Bytes apart from the stack the function uses, in a memory that differs
from `s`'s only in the frame. -/
theorem bytes_keep {s : State} {m : Mem} (hm : Frame [⟨fb s, 272⟩] s.mem m) {p : Addr} {n : Nat}
    (hR : (bigR s).Disjoint ⟨p, n⟩) (hl : n < 2 ^ 64) : Spec.Rsa.bytesAt m p n = Spec.Rsa.bytesAt s.mem p n :=
  Proof.Rsa.rsa_bytes_frame hm hl fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hR.sub_left (frame_big s)).symm

/-- A region apart from the stack the function uses is not all of memory. -/
theorem len_lt {s : State} {p : Addr} {n : Nat} (hR : (bigR s).Disjoint ⟨p, n⟩) : n < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun h => hR (kb s) (Region.contains_self' (by unfold fStack; decide)) ?_
  simp only [Region.Contains]
  have := (kb s - p).isLt
  omega_using [this, h]

theorem words_keep {s : State} {m : Mem} (hm : Frame [⟨fb s, 272⟩] s.mem m) {p : Addr} {n : Nat}
    (hR : (bigR s).Disjoint ⟨p, n * 8⟩) : Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n :=
  Proof.Rsa.wordsAt_frame hm (by have := len_lt hR; omega_using [this]) fun r hr => by
    rw [List.mem_singleton.mp hr, Nat.mul_comm]; exact (hR.sub_left (frame_big s)).symm

/-- `PreX` at the callee's entry. -/
theorem prex_entry {s x : State} (hx : PreX s) (big : Big s) (hsp : x.sp = fb s)
    (hg : ∀ r ∈ argRegs, x.gpr r = s.gpr r) (ha : ∀ j < 17, stackArg x j = stackArg s j)
    (hm : Frame [⟨fb s, 272⟩] s.mem x.mem) : PreX x := by
  have g3 := hg .r3 (by decide)
  have g4 := hg .r4 (by decide)
  have g5 := hg .r5 (by decide)
  have g6 := hg .r6 (by decide)
  have g7 := hg .r7 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have a6 := ha 6 (by decide)
  have a13 := ha 13 (by decide)
  have a14 := ha 14 (by decide)
  have a15 := ha 15 (by decide)
  have a16 := ha 16 (by decide)
  have eK : kR x = kF s := by simp only [kR, hsp, stackBytes_eq]
  refine ⟨by simpa only [oR, preR, g3, g4, a15, a16] using hx.oP, by simpa only [mlR, preR, g5, a15, a16] using hx.mP,
    by simpa only [sR, preR, a13, a14, a15, a16] using hx.sP,
    by rw [eK]; simpa only [preR, a15, a16] using big.kP.sub_left (kF_sub s),
    by simpa only [a15, a16] using hx.wP, by simpa only [g7, a4, a6, a16] using hx.pl, fun _ => ?_⟩
  rw [g6, g7, a3, a4, a5, a6, a15, a16, bytes_keep hm big.kn (BitVec.isLt _), bytes_keep hm big.kp (BitVec.isLt _),
    bytes_keep hm big.kq (BitVec.isLt _), words_keep hm big.kP]
  exact hx.hyp rfl

/-- The outcome of the decryption of `s`'s arguments. -/
abbrev decOf (s : State) : Spec.Rsa.Outcome :=
  Spec.RsaPkcs1Enc.decrypt (Spec.Rsa.bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (Dec.dOf s)
    (Spec.Rsa.bytesAt s.mem (stackArg s 3) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 5) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 7) (stackArg s 4).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 9) (stackArg s 6).toNat)
    (Spec.Rsa.bytesAt s.mem (stackArg s 11) (stackArg s 4).toNat) (Dec.cOf s)

theorem decOf_entry {s x : State} (hp : DPre true s) (big : Big s)
    (hg : ∀ r ∈ argRegs, x.gpr r = s.gpr r) (ha : ∀ j < 17, stackArg x j = stackArg s j)
    (hm : Frame [⟨fb s, 272⟩] s.mem x.mem) : decOf x = decOf s := by
  have g6 := hg .r6 (by decide)
  have g7 := hg .r7 (by decide)
  have g8 := hg .r8 (by decide)
  have g9 := hg .r9 (by decide)
  have g10 := hg .r10 (by decide)
  have a0 := ha 0 (by decide)
  have a1 := ha 1 (by decide)
  have a3 := ha 3 (by decide)
  have a4 := ha 4 (by decide)
  have a5 := ha 5 (by decide)
  have a6 := ha 6 (by decide)
  have a7 := ha 7 (by decide)
  have a9 := ha 9 (by decide)
  have a11 := ha 11 (by decide)
  have h8 := hp.h8
  have h10 := hp.h10
  have h12 := hp.h12
  have hi := hp.hi
  have kdp : (bigR s).Disjoint ⟨stackArg s 7, (stackArg s 4).toNat⟩ := by rw [← h8]; exact big.kdp
  have kdq : (bigR s).Disjoint ⟨stackArg s 9, (stackArg s 6).toNat⟩ := by rw [← h10]; exact big.kdq
  have kqi : (bigR s).Disjoint ⟨stackArg s 11, (stackArg s 4).toNat⟩ := by rw [← h12]; exact big.kqi
  have ki : (bigR s).Disjoint ⟨stackArg s 1, (s.gpr .r7).toNat⟩ := by rw [← hi]; exact big.ki
  simp only [decOf, Dec.dOf, Dec.cOf, g6, g7, g8, g9, g10, a0, a1, a3, a4, a5, a6, a7, a9, a11]
  rw [bytes_keep hm big.kn (BitVec.isLt _), bytes_keep hm big.ke (BitVec.isLt _),
    bytes_keep hm big.kd (BitVec.isLt _), bytes_keep hm big.kp (BitVec.isLt _),
    bytes_keep hm big.kq (BitVec.isLt _), bytes_keep hm kdp (BitVec.isLt _), bytes_keep hm kdq (BitVec.isLt _),
    bytes_keep hm kqi (BitVec.isLt _), bytes_keep hm ki (BitVec.isLt _)]

/-- What the call leaves. -/
structure Called (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr
  g : ∀ r ∈ preserved, r ∉ setRegs → t.gpr r = s.gpr r
  g14 : t.gpr .r14 = s.gpr .r3
  g15 : t.gpr .r15 = s.gpr .r4
  g16 : t.gpr .r16 = s.gpr .r5
  g17 : t.gpr .r17 = stackArg s 13
  fr : Frame [oR s, mlR s, sR s, bigR s] s.mem t.mem
  sl : Slots s t.mem
  post : Proof.RsaPkcs1Enc.writtenMsg t.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r7).toNat ((t.gpr .r3).setWidth 32)
    (decOf s)

/-- The callee's entry. -/
abbrev entry (s t : State) : State := t.callEntry.withRegions (RD s) (WR s)

theorem entry_facts {s t : State} (ht : Set s t) :
    (entry s t).sp = fb s ∧ (∀ r ∈ argRegs, (entry s t).gpr r = s.gpr r) ∧
      (∀ j < 17, stackArg (entry s t) j = stackArg s j) ∧ (entry s t).mem = t.mem := by
  have esp : (entry s t).sp = fb s := ht.sp
  refine ⟨esp, fun r hr => ?_, fun j hj => ?_, rfl⟩
  · rw [State.withRegions_gpr, State.callEntry_gpr _ (by revert r; decide)]
    exact ht.g r (by revert r; decide)
  · show t.mem.readW (stackArgAddr (entry s t) j) 64 = _
    rw [stackArgAddr, esp, show 32 + 8 * (8 + j) = 96 + 8 * j by omega_using []]
    exact ht.sl.copy j hj

/-- The regions the callee is given are ours. -/
theorem entry_covers {s t : State} (hp : DPre true s) (ht : Set s t) :
    Covers (RD s ++ WR s) (t.rd ++ t.wr) ∧ Covers (WR s) t.wr := by
  have hw : Covers (WR s) t.wr := Covers.of_mem fun r hr => by
    rw [ht.wr, hp.hwr]; exact List.mem_cons_of_mem _ hr
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  simp only [RD, List.mem_cons, List.not_mem_nil, or_false] at hr
  have hl : ∀ R ∈ s.rd, Covers [R] (t.rd ++ t.wr) := fun R hR =>
    Covers.left (Covers.of_mem fun x hx => by rw [List.mem_singleton.mp hx, ht.rd]; exact hR)
  rw [hp.hrd] at hl
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact hl _ (by simp)
  · exact Covers.right (Covers.one (by rw [ht.wr]; exact ⟨_, List.mem_cons_self .., Offset.contains _ (by decide) (by decide) (by decide)⟩))

/-- The call of `vg_rsa_pkcs1_decrypt_precomputed`, by its contract. -/
theorem call_ok {c : Prog isa} (hv : ∀ s, K.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ K.post s s')
    (hd : sdepth c ≤ 3648) {name : String} {s t : State} (hp : DPre true s) (hx : PreX s) (big : Big s)
    (ht : Set s t) : WP isa (.call name c) t (Called s) := by
  obtain ⟨esp, eg, ea, em⟩ := entry_facts ht
  have hm : Frame [⟨fb s, 272⟩] s.mem (entry s t).mem := by rw [em]; exact ht.fr
  have dp := dpre_entry hp big esp eg ea rfl rfl
  have xp := prex_entry hx big esp eg ea hm
  obtain ⟨hc, hw⟩ := entry_covers hp ht
  refine WP.callAny (rd := RD s) (wr := WR s) hv (dec_pre_of dp xp) hc hw
    (fun t' hrd hwr hsp hf hpres hpost => ?_) (by omega_using [hd])
  have hpost' : Proof.RsaPkcs1Enc.writtenMsg t'.mem ((entry s t).gpr .r3) ((entry s t).gpr .r5)
      ((entry s t).gpr .r7).toNat ((t'.gpr .r3).setWidth 32) (decOf (entry s t)) := dec_post hpost
  rw [eg .r3 (by decide), eg .r5 (by decide), eg .r7 (by decide), decOf_entry hp big eg ea hm] at hpost'
  have hbelow : Region.Sub (below t.sp (sdepth c)) (bigR s) := fun x hx =>
    kF_sub s x (by rw [ht.sp] at hx; exact Offset.sub_below (fb s) hd (by omega_using [hd]) x hx)
  have hfr : Frame [oR s, mlR s, sR s, bigR s] s.mem t'.mem := by
    refine Frame.trans (Frame.sub ht.fr fun r hr => ⟨bigR s, by simp, by rw [List.mem_singleton.mp hr]; exact frame_big s⟩)
      (Frame.sub hf fun r hr => ?_)
    simp only [WR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, hbelow⟩
  have slB : Region.Sub (slR s) (bigR s) := fslot_sub s (by decide)
  have hsl : Slots s t'.mem := ht.sl.frame hf fun r hr => by
    simp only [WR, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact big.ko.sub_left slB
    · exact big.km.sub_left slB
    · exact big.ks.sub_left slB
    · rw [ht.sp]; exact Offset.disjoint_below _ (by have := big.sp; omega_using [hd])
  exact ⟨hsp.trans ht.sp, hrd.trans ht.rd, hwr.trans ht.wr, fun r hr hr' => (hpres r hr).trans (ht.g r hr'),
    (hpres _ (by decide)).trans ht.g14, (hpres _ (by decide)).trans ht.g15, (hpres _ (by decide)).trans ht.g16,
    (hpres _ (by decide)).trans ht.g17, hfr, hsl, hpost'⟩

/-! ## After the call -/

theorem inR_right {rd wr : List Region} {a : Addr} {n : Nat} (h : InRegions wr a n) : InRegions (rd ++ wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

open VG.WriteBytes (writeBytes)

/-- `scratch`. -/
abbrev scr (s : State) : Addr := stackArg s 13

/-- The bytes of `m` from `S`. -/
def vw (m : Mem) (S : Addr) (o : Nat) : Byte := m (S + BitVec.ofNat 64 o)

theorem vw_wb (m : Mem) (S : Addr) (xs : List Byte) {o : Nat} (ho : o < 2 ^ 64) :
    vw (writeBytes m S xs) S o = if o < xs.length then xs.getD o 0 else vw m S o := by
  simp only [vw, writeBytes, Mem.sub_ofNat_toNat S ho]

/-- During the tail: the frame, the registers, and the result `R` in `r3`. -/
structure Mid (s : State) (R : BitVec 64) (v : State) : Prop where
  sp : v.sp = fb s
  rd : v.rd = s.rd
  wr : v.wr = ⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr
  lr : v.lr = s.lr
  g : ∀ r ∈ preserved, r ∉ setRegs → v.gpr r = s.gpr r
  g14 : v.gpr .r14 = s.gpr .r3
  g15 : v.gpr .r15 = s.gpr .r4
  g16 : v.gpr .r16 = s.gpr .r5
  g17 : v.gpr .r17 = scr s
  r3 : v.gpr .r3 = R
  sl : Slots s v.mem

/-- The registers the tail writes. -/
abbrev tmpRegs : List Reg := [.r0, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem Mid.step {s v v' : State} {R : BitVec 64} (h : Mid s R v) {rs : List Reg} (k : Keep rs v v')
    (hrs : ∀ r ∈ rs, r ∈ tmpRegs) {Xs : List Region} (hf : Frame Xs v.mem v'.mem)
    (hd : ∀ X ∈ Xs, (slR s).Disjoint X) : Mid s R v' := by
  have g : ∀ r, r ∉ tmpRegs → v'.gpr r = v.gpr r := fun r hr => k.gpr r fun h' => hr (hrs r h')
  exact ⟨k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr, k.lr.trans h.lr,
    fun r hr hr' => (g r (by revert r; decide)).trans (h.g r hr hr'), (g _ (by decide)).trans h.g14,
    (g _ (by decide)).trans h.g15, (g _ (by decide)).trans h.g16, (g _ (by decide)).trans h.g17,
    (g _ (by decide)).trans h.r3, h.sl.frame hf hd⟩

/-- The return address back. -/
theorem after_ok {s t : State} (hc : Called s t) :
    WP isa (.block Impl.RsaPkcs1Enc.PPC64LE.Front.after) t fun v => Mid s (t.gpr .r3) v ∧ v.mem = t.mem := by
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  refine wp_ld (a := fb s + BitVec.ofNat 64 oLr) (by rw [e₁, hc.sp, BitVec.add_zero])
    (by rw [o₁.rd, o₁.wr, hc.wr]; exact inR_right (frame_in s (by decide) (by decide)))
    fun u₂ o₂ e₂ => ?_
  refine wp_mtlr fun u₃ g₃ m₃ r₃ w₃ p₃ l₃ => wp_nil ?_
  have k : Only [.r12, .r0] t u₂ := (o₁.trans o₂).mono
  have g : ∀ r, r ∉ [Reg.r12, .r0] → u₃.gpr r = t.gpr r := fun r hr => by rw [g₃]; exact k.gpr r hr
  refine ⟨⟨by rw [p₃, k.sp, hc.sp], by rw [r₃, k.rd, hc.rd], by rw [w₃, k.wr, hc.wr], ?_,
    fun r hr hr' => (g r (by revert r; decide)).trans (hc.g r hr hr'), (g _ (by decide)).trans hc.g14,
    (g _ (by decide)).trans hc.g15, (g _ (by decide)).trans hc.g16, (g _ (by decide)).trans hc.g17,
    g _ (by decide), by rw [m₃, k.mem]; exact hc.sl⟩, by rw [m₃, k.mem]⟩
  rw [l₃, e₂, o₁.mem, show (oLr : Nat) = 264 from rfl]
  exact hc.sl.slr

/-! ### The buffer -/

section
variable {s : State} {R : BitVec 64} (hp : DPre true s) (big : Big s)
include hp big

omit big in
/-- `scratch` holds at least 2048 bytes. -/
theorem scr_len : 2048 ≤ (stackArg s 14).toNat * 8 := by
  have hs := hp.hs; have k1 := hp.k1; unfold Spec.Rsa.scratchWords at *; omega_using [hs, k1]

omit big in
theorem scr_in {v : State} (h : Mid s R v) {o : Nat} (ho : o < 2048) : InRegions v.wr (scr s + BitVec.ofNat 64 o) 1 := by
  rw [h.wr, hp.hwr]
  have := scr_len hp
  exact ⟨sR s, by simp, Offset.contains_base _ (by omega_using [ho, this]) (by omega_using [ho])⟩

omit big in
theorem scr_sub {n : Nat} (hn : n ≤ 2048) : Region.Sub ⟨scr s, n⟩ (sR s) := by
  have := scr_len hp
  exact Region.sub_prefix (by omega_using [hn, this])

theorem slR_scr {n : Nat} (hn : n ≤ 2048) : (slR s).Disjoint ⟨scr s, n⟩ :=
  (big.ks.sub_left (fslot_sub s (by decide))).sub_right (scr_sub hp hn)

omit hp in
theorem slR_out : (slR s).Disjoint (oR s) := big.ko.sub_left (fslot_sub s (by decide))

omit big in
theorem scr_fit : (scr s).toNat + 2048 ≤ 2 ^ 64 := by
  show (stackArg s 13).toNat + 2048 ≤ 2 ^ 64
  have ws := hp.ws; have sl := scr_len hp; omega_using [ws, sl]

omit big in
theorem out_in {v : State} (h : Mid s R v) {o : Nat} (ho : o < (s.gpr .r4).toNat) :
    InRegions v.wr (s.gpr .r3 + BitVec.ofNat 64 o) 1 := by
  rw [h.wr, hp.hwr]
  have := hp.wo
  exact ⟨oR s, by simp, Offset.contains_base _ (by omega_using [ho]) (by omega_using [ho, this])⟩

omit big in
theorem out_scr {i j : Nat} (hi : i < (s.gpr .r4).toNat) (hj : j < 2048) :
    s.gpr .r3 + BitVec.ofNat 64 i ≠ scr s + BitVec.ofNat 64 j := by
  have sl := scr_len hp
  intro e
  refine hp.os (s.gpr .r3 + BitVec.ofNat 64 i) (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) ?_
  rw [e]; exact Offset.contains_base _ (by omega_using [hj, sl]) (by omega_using [hj])

/-- The buffer cleared. -/
theorem clear_ok {v : State} (h : Mid s R v) :
    WP isa Impl.RsaPkcs1Enc.PPC64LE.Front.clearBuf v fun v' => Mid s R v' ∧
      v'.mem = writeBytes v.mem (scr s) (List.replicate 2048 0) := by
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_li (by decide) fun u₂ o₂ e₂ => wp_li (by decide) fun u₃ o₃ e₃ => wp_nil ?_)
  have k : Only [.r4, .r5, .r6] v u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (VG.Proof.RsaOaep.PPC64LE.zero_ok (p := scr s) (n := 2048) (b := 0) (by decide) (by decide)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.g17]) (by rw [o₃.get .r5, e₂]) (by rw [e₃]; rfl)
    (fun i hi => by rw [k.wr]; exact scr_in hp h hi)) fun u ⟨ku, hm⟩ => ?_
  have hm' : u.mem = writeBytes v.mem (scr s) (List.replicate 2048 0) := by rw [hm, k.mem]
  refine ⟨(h.step (k.keep.trans ku) (by decide) (Xs := [⟨scr s, 2048⟩])
    (by rw [hm']; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [List.length_replicate]; exact Region.contains_self' (Nat.le_refl _)))
    fun X hX => by rw [List.mem_singleton.mp hX]; exact slR_scr hp big (Nat.le_refl _)), hm'⟩

/-- `out`'s `k` bytes to the buffer. -/
theorem copyIn_ok {v : State} (h : Mid s R v) :
    WP isa Impl.RsaPkcs1Enc.PPC64LE.Front.copyIn v fun v' => Mid s R v' ∧
      v'.mem = writeBytes v.mem (scr s) (Spec.Rsa.bytesAt v.mem (s.gpr .r3) (s.gpr .r4).toNat) := by
  have hk1 := hp.k1; have hk2 := hp.k2; have h4 := hp.h4
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_nil ?_)
  have k : Only [.r4, .r5, .r6] v u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (VG.Proof.RsaOaep.PPC64LE.copy_ok (q := s.gpr .r3) (p := scr s) (n := (s.gpr .r4).toNat)
    (by omega_using [hk1, h4]) (BitVec.isLt _)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.g14]) (by rw [o₃.get .r5, e₂, o₁.get .r17, h.g17])
    (by rw [e₃, o₂.get .r15, o₁.get .r15, h.g15, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by rw [k.rd, k.wr]; exact inR_right (out_in hp h hj))
    (fun i hi => by rw [k.wr]; exact scr_in hp h (by omega_using [hi, hk2, h4]))
    (fun j hj i hi => out_scr hp hj (by omega_using [hi, hk2, h4]))) fun u ⟨ku, hm⟩ => ?_
  have hm' : u.mem = writeBytes v.mem (scr s) (Spec.Rsa.bytesAt v.mem (s.gpr .r3) (s.gpr .r4).toNat) := by
    rw [hm, k.mem]
  refine ⟨(h.step (k.keep.trans ku) (by decide) (Xs := [⟨scr s, 2048⟩])
    (by rw [hm']; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact Region.contains_self' (by omega_using [hk2, h4])))
    fun X hX => by rw [List.mem_singleton.mp hX]; exact slR_scr hp big (Nat.le_refl _)), hm'⟩

/-- The buffer's first `k` bytes to `out`. -/
theorem copyOut_ok {v : State} (h : Mid s R v) :
    WP isa Impl.RsaPkcs1Enc.PPC64LE.Front.copyOut v fun v' => Mid s R v' ∧
      v'.mem = writeBytes v.mem (s.gpr .r3) (Spec.Rsa.bytesAt v.mem (scr s) (s.gpr .r4).toNat) := by
  have hk1 := hp.k1; have hk2 := hp.k2; have h4 := hp.h4
  have wo := hp.wo
  refine WP.seq (wp_mov fun u₁ o₁ e₁ => wp_mov fun u₂ o₂ e₂ => wp_mov fun u₃ o₃ e₃ => wp_nil ?_)
  have k : Only [.r4, .r5, .r6] v u₃ := (o₁.trans (o₂.trans o₃)).mono
  refine WP.mono (VG.Proof.RsaOaep.PPC64LE.copy_ok (q := scr s) (p := s.gpr .r3) (n := (s.gpr .r4).toNat)
    (by omega_using [hk1, h4]) (BitVec.isLt _)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, h.g17]) (by rw [o₃.get .r5, e₂, o₁.get .r14, h.g14])
    (by rw [e₃, o₂.get .r15, o₁.get .r15, h.g15, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    (fun j hj => by rw [k.rd, k.wr]; exact inR_right (scr_in hp h (by omega_using [hj, hk2, h4])))
    (fun i hi => by rw [k.wr]; exact out_in hp h hi)
    (fun j hj i hi => (out_scr hp hi (by omega_using [hj, hk2, h4])).symm)) fun u ⟨ku, hm⟩ => ?_
  have hm' : u.mem = writeBytes v.mem (s.gpr .r3) (Spec.Rsa.bytesAt v.mem (scr s) (s.gpr .r4).toNat) := by
    rw [hm, k.mem]
  refine ⟨(h.step (k.keep.trans ku) (by decide) (Xs := [oR s])
    (by rw [hm']; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact Region.contains_self' (Nat.le_refl _)))
    fun X hX => by rw [List.mem_singleton.mp hX]; exact slR_out big), hm'⟩

end

/-- What the function leaves before the frame is freed. -/
structure Fin (s : State) (R : BitVec 64) (v : State) : Prop where
  sp : v.sp = fb s
  wr : v.wr = ⟨fb s + BitVec.ofNat 64 32, 240⟩ :: s.wr
  lr : v.lr = s.lr
  g : ∀ r ∈ preserved, v.gpr r = s.gpr r
  r3 : v.gpr .r3 = R

/-- Our caller's `r14`–`r17` back. -/
theorem restore_ok {s v : State} {R : BitVec 64} (h : Mid s R v) :
    WP isa (.block Impl.RsaPkcs1Enc.PPC64LE.Front.restore) v fun v' => Fin s R v' ∧ v'.mem = v.mem := by
  have hin : ∀ {d : Nat}, 32 ≤ d → d + 8 ≤ 272 → InRegions (v.rd ++ v.wr) (fb s + BitVec.ofNat 64 d) 8 :=
    fun h₁ h₂ => by rw [h.wr]; exact inR_right (frame_in s h₁ h₂)
  refine wp_addSp fun u₁ o₁ e₁ => ?_
  have a : ∀ d : Nat, u₁.gpr .r12 + BitVec.ofNat 64 d = fb s + BitVec.ofNat 64 d := fun d => by
    rw [e₁, h.sp, BitVec.add_zero]
  refine wp_ld (a := fb s + BitVec.ofNat 64 o14) (a _) (by rw [o₁.rd, o₁.wr]; exact hin (by decide) (by decide))
    fun u₂ o₂ e₂ => ?_
  refine wp_ld (a := fb s + BitVec.ofNat 64 o15) (by rw [o₂.get .r12]; exact a _)
    (by rw [o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact hin (by decide) (by decide)) fun u₃ o₃ e₃ => ?_
  refine wp_ld (a := fb s + BitVec.ofNat 64 o16) (by rw [o₃.get .r12, o₂.get .r12]; exact a _)
    (by rw [o₃.rd, o₃.wr, o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact hin (by decide) (by decide)) fun u₄ o₄ e₄ => ?_
  refine wp_ld (a := fb s + BitVec.ofNat 64 o17) (by rw [o₄.get .r12, o₃.get .r12, o₂.get .r12]; exact a _)
    (by rw [o₄.rd, o₄.wr, o₃.rd, o₃.wr, o₂.rd, o₂.wr, o₁.rd, o₁.wr]; exact hin (by decide) (by decide))
    fun u₅ o₅ e₅ => wp_nil ?_
  have k : Only [.r12, .r14, .r15, .r16, .r17] v u₅ := (o₁.trans (o₂.trans (o₃.trans (o₄.trans o₅)))).mono
  have hm : u₅.mem = v.mem := k.mem
  refine ⟨⟨by rw [k.sp, h.sp], by rw [k.wr, h.wr], by rw [k.lr, h.lr], fun r hr => ?_, by rw [k.get .r3, h.r3]⟩, hm⟩
  by_cases h14 : r = .r14
  · subst h14; rw [o₅.get .r14, o₄.get .r14, o₃.get .r14, e₂, o₁.mem]; exact h.sl.s14
  by_cases h15 : r = .r15
  · subst h15; rw [o₅.get .r15, o₄.get .r15, e₃, o₂.mem, o₁.mem]; exact h.sl.s15
  by_cases h16 : r = .r16
  · subst h16; rw [o₅.get .r16, e₄, o₃.mem, o₂.mem, o₁.mem]; exact h.sl.s16
  by_cases h17 : r = .r17
  · subst h17; rw [e₅, o₄.mem, o₃.mem, o₂.mem, o₁.mem]; exact h.sl.s17
  have h12 : r ≠ .r12 := by rintro rfl; simp [preserved] at hr
  have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
  rw [k.gpr r (by simp [h12, h14, h15, h16, h17])]
  exact h.g r hr (by simp [setRegs, h0, h12, h14, h15, h16, h17])

/-! ### The shift -/

open VG.Proof.RsaPss.PPC64LE (passV shV shV_out)
open VG.Proof.Mgf1 (ifp ifn)

/-- Eleven passes by the bits of `a < 2^11`, the `j`-th by `2^j`, shift the
`n` bytes from `b` left by `a`, zeros coming in from after them, if the
`2^10` bytes after them are zero (`shV_in` with eleven passes). -/
theorem shV_in11 (V : Nat → Byte) (b n a : Nat) (hz : ∀ x, n ≤ x → x < n + 2 ^ 10 → V (b + x) = 0) :
    ∀ j ≤ 11, ∀ i < n, shV V b n a j (b + i) = if i + a % 2 ^ j < n then V (b + (i + a % 2 ^ j)) else 0
  | 0, _, i, hi => by simp only [shV, Nat.pow_zero, Nat.mod_one, Nat.add_zero]; rw [ifp hi]
  | j + 1, hj, i, hi => by
    have ih := shV_in11 V b n a hz j (by omega_using [hj])
    have hm : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * (a / 2 ^ j % 2) := Nat.mod_pow_succ
    have hp : 2 ^ j ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega_using [hj])
    rw [shV, passV, ifp ⟨by omega_using [], by omega_using [hi]⟩]
    by_cases hb : a / 2 ^ j % 2 = 1
    · rw [ifp (decide_eq_true hb), show b + i + 2 ^ j = b + (i + 2 ^ j) by omega_using []]
      rw [hb, Nat.mul_one] at hm
      rw [hm]
      by_cases hl : i + 2 ^ j < n
      · rw [ih (i + 2 ^ j) hl, show i + 2 ^ j + a % 2 ^ j = i + (a % 2 ^ j + 2 ^ j) by omega_using []]
      · rw [shV_out V b n a j _ (by omega_using [hl]), hz _ (by omega_using [hl]) (by omega_using [hi, hp]),
          ifn (by omega_using [hl])]
    · have hb0 : a / 2 ^ j % 2 = 0 := by omega_using [hb]
      rw [ifn (by simpa using hb), hm, hb0, Nat.mul_zero, Nat.add_zero, ih i hi]

theorem vw_w8 (m : Mem) (S : Addr) (b : Byte) {d o : Nat} (hd : d < 2 ^ 32) (ho : o < 2 ^ 32) :
    vw (m.writeW (S + BitVec.ofNat 64 d) b) S o = if o = d then b else vw m S o := by
  simp only [vw]
  rw [VG.WriteBytes.writeW8_apply]
  by_cases h : o = d
  · subst h; simp
  · rw [ifn (Offset.add_ofNat_ne S (by omega_using [ho]) (by omega_using [hd]) h), ifn h]

section
variable {s : State} {R : BitVec 64} (hp : DPre true s) (big : Big s)
include hp big

/-- A pass, by bit 0 of `x` (`r8`) and `d` bytes (`r9`). -/
theorem pass_ok {v : State} (h : Mid s R v) {x d : Nat} (h8 : v.gpr .r8 = BitVec.ofNat 64 x)
    (h9 : v.gpr .r9 = BitVec.ofNat 64 d) (hd : d ≤ 1024) :
    WP isa Impl.RsaPkcs1Enc.PPC64LE.Front.shiftPass v fun v' => Mid s R v' ∧
      Keep [.r4, .r5, .r6, .r7, .r11, .r12] v v' ∧ Frame [⟨scr s, 1024⟩] v.mem v'.mem ∧
      ∀ o < 2048, vw v'.mem (scr s) o = passV (vw v.mem (scr s)) 0 1024 (x % 2 = 1) d o := by
  let V := vw v.mem (scr s)
  let bit : Bool := x % 2 = 1
  refine WP.seq (wp_mov fun t₁ o₁ e₁ => wp_add fun t₂ o₂ e₂ =>
    wp_li (by decide) fun t₃ o₃ e₃ => wp_and fun t₄ o₄ e₄ => wp_li (by decide) fun t₅ o₅ e₅ =>
    wp_sub fun t₆ o₆ e₆ => wp_li (by decide) fun t₇ o₇ e₇ => wp_nil ?_)
  have k₇ : Only [.r4, .r5, .r6, .r7] v t₇ :=
    (o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono
  have a4 : t₁.gpr .r4 = scr s := by rw [e₁, h.g17]
  have g6 : t₇.gpr .r6 = if bit then BitVec.allOnes 64 else 0#64 := by
    rw [o₇.get .r6, e₆, e₅, o₅.get .r6, e₄, e₃, o₃.get .r8, o₂.get .r8, o₁.get .r8, h8,
      VG.Proof.RsaOaep.PPC64LE.Dec.mask_odd]
    simp only [bit, decide_eq_true_eq]
  have m₇ := h.step k₇.keep (by decide) (Xs := []) (by rw [k₇.mem]; exact Frame.refl _ _) (by simp)
  refine WP.mono (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_countdown (cnt := .r7) (N := 1024) (by decide) (by decide)
    (fun i u => Mid s R u ∧ Keep [.r4, .r5, .r7, .r11, .r12] t₇ u ∧
      u.gpr .r4 = scr s + BitVec.ofNat 64 i ∧ u.gpr .r5 = scr s + BitVec.ofNat 64 (i + d) ∧
      Frame [⟨scr s, 1024⟩] v.mem u.mem ∧
      ∀ o < 2048, vw u.mem (scr s) o = if o < i then (if bit then V (o + d) else V o) else V o) ?_
    ⟨m₇, Keep.refl _ _, by rw [o₇.get .r4, o₆.get .r4, o₅.get .r4, o₄.get .r4, o₃.get .r4, o₂.get .r4, a4,
      BitVec.add_zero],
      by rw [o₇.get .r5, o₆.get .r5, o₅.get .r5, o₄.get .r5, o₃.get .r5, e₂, a4, o₁.get .r9, h9, Nat.zero_add],
      by rw [k₇.mem]; exact Frame.refl _ _, fun o _ => by rw [ifn (by omega_using []), k₇.mem]⟩ (by rw [e₇]))
    fun u ⟨mu, ku, _, _, fu, vu⟩ => ⟨mu, (k₇.keep.trans ku).mono, fu, fun o ho => by
      rw [vu o ho]; simp only [passV, Nat.zero_le, true_and, Nat.zero_add]; rfl⟩
  intro i hi u ⟨mu, ku, u4, u5, fu, vu⟩ _
  have hsc := scr_fit hp
  refine wp_lbz (a := scr s + BitVec.ofNat 64 i) (by rw [u4, BitVec.add_zero])
    (inR_right (scr_in hp mu (by omega_using [hi]))) fun u₁ p₁ f₁ => ?_
  refine wp_lbz (a := scr s + BitVec.ofNat 64 (i + d)) (by rw [p₁.get .r5, u5, BitVec.add_zero])
    (by rw [p₁.rd, p₁.wr]; exact inR_right (scr_in hp mu (by omega_using [hi, hd]))) fun u₂ p₂ f₂ => ?_
  refine wp_xor fun u₃ p₃ f₃ => wp_and fun u₄ p₄ f₄ => wp_xor fun u₅ p₅ f₅ => ?_
  have k₅ : Only [.r11, .r12] u u₅ := (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))).mono
  refine wp_stb (a := scr s + BitVec.ofNat 64 i) (by rw [k₅.get .r4, u4, BitVec.add_zero])
    (by rw [k₅.wr]; exact scr_in hp mu (by omega_using [hi])) fun u₆ m₆ => ?_
  refine wp_addi fun u₇ p₇ f₇ => wp_addi fun u₈ p₈ f₈ => wp_subi fun u₉ p₉ f₉ => wp_nil ?_
  have hm0 : u₅.mem = u.mem := k₅.mem
  have va : u.mem (scr s + BitVec.ofNat 64 i) = V i := by
    have := vu i (by omega_using [hi]); rw [ifn (by omega_using [])] at this; exact this
  have vb : u₁.mem (scr s + BitVec.ofNat 64 (i + d)) = V (i + d) := by
    have := vu (i + d) (by omega_using [hi, hd]); rw [ifn (by omega_using [])] at this; rw [p₁.mem]; exact this
  have hb : (u₅.gpr .r11).setWidth 8 = if bit then V (i + d) else V i := by
    rw [f₅, p₄.get .r11, p₃.get .r11, p₂.get .r11, f₁, f₄, f₃, f₂, p₂.get .r11, f₁, va, vb, p₃.get .r6,
      p₂.get .r6, p₁.get .r6, ku.get .r6, g6]
    exact VG.Proof.RsaOaep.PPC64LE.Dec.sel_byte _ _ bit
  have q : Keep [.r11, .r12, .r4, .r5, .r7] u u₉ :=
    (k₅.keep.trans (m₆.keep.trans (p₇.keep.trans (p₈.keep.trans p₉.keep)))).mono
  have hm : u₉.mem = u.mem.writeW (scr s + BitVec.ofNat 64 i) (if bit then V (i + d) else V i) := by
    rw [p₉.mem, p₈.mem, p₇.mem, m₆.mem, hb, hm0]
  have hf : Frame [⟨scr s, 1024⟩] u.mem u₉.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
  refine ⟨⟨mu.step q (by decide) hf fun X hX => by
      rw [List.mem_singleton.mp hX]; exact slR_scr hp big (by decide), (ku.trans q).mono, ?_, ?_, fu.trans hf,
    fun o ho => ?_⟩, ?_⟩
  · rw [p₉.get .r4, p₈.get .r4, f₇, m₆.gpr, k₅.get .r4, u4, VG.Proof.RsaPkcs1Sig.PPC64LE.ofNat_succ']
  · rw [p₉.get .r5, f₈, p₇.get .r5, m₆.gpr, k₅.get .r5, u5, VG.Proof.RsaPkcs1Sig.PPC64LE.ofNat_succ',
      show i + d + 1 = i + 1 + d by omega_using []]
  · rw [hm, vw_w8 _ _ _ (by omega_using [hi]) (by omega_using [ho]), vu o ho]
    by_cases e : o = i
    · subst e
      rw [ifp rfl, ifp (show o < o + 1 by omega_using [])]
    · rw [ifn e]
      by_cases e' : o < i
      · rw [ifp e', ifp (show o < i + 1 by omega_using [e'])]
      · rw [ifn e', ifn (show ¬ o < i + 1 by omega_using [e, e'])]
  · rw [f₉, p₈.get .r7, p₇.get .r7, m₆.gpr, k₅.get .r7]


/-- The shift: the buffer's first 1024 bytes by `k - L`, `L` the word at
`msg_len`, in eleven passes. -/
theorem shift_ok {v : State} (h : Mid s R v) {L : Nat} (hL : v.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 L)
    (hLk : L ≤ (s.gpr .r4).toNat) :
    WP isa Impl.RsaPkcs1Enc.PPC64LE.Front.shift v fun v' => Mid s R v' ∧ Frame [⟨scr s, 1024⟩] v.mem v'.mem ∧
      ∀ o < 2048, vw v'.mem (scr s) o = shV (vw v.mem (scr s)) 0 1024 ((s.gpr .r4).toNat - L) 11 o := by
  have wm := hp.wm
  refine WP.seq (wp_ld (a := s.gpr .r5) (by rw [h.g16, BitVec.add_zero])
    (by rw [h.rd, h.wr, hp.hwr]
        exact inR_right ⟨mlR s, by simp, Region.contains_self' (Nat.le_refl _)⟩) fun t₁ o₁ e₁ => ?_)
  refine wp_sub fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ => wp_li (by decide) fun t₄ o₄ e₄ => wp_nil ?_
  have k₄ : Only [.r8, .r9, .r10] v t₄ := (o₁.trans (o₂.trans (o₃.trans o₄))).mono
  let a := (s.gpr .r4).toNat - L
  let V := vw v.mem (scr s)
  have r8 : t₄.gpr .r8 = BitVec.ofNat 64 a := by
    rw [o₄.get .r8, o₃.get .r8, e₂, o₁.get .r15, h.g15, e₁, hL]
    have e4 : s.gpr .r4 = BitVec.ofNat 64 (s.gpr .r4).toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (congrArg (· - BitVec.ofNat 64 L) e4).trans (Offset.ofNat_sub_ofNat hLk)
  have m₄ := h.step k₄.keep (by decide) (Xs := []) (by rw [k₄.mem]; exact Frame.refl _ _) (by simp)
  refine WP.mono (VG.Proof.RsaPkcs1Sig.PPC64LE.wp_countdown (cnt := .r10) (N := 11) (by decide) (by decide)
    (fun j u => Mid s R u ∧ u.gpr .r8 = BitVec.ofNat 64 (a / 2 ^ j) ∧ u.gpr .r9 = BitVec.ofNat 64 (2 ^ j) ∧
      Frame [⟨scr s, 1024⟩] v.mem u.mem ∧ ∀ o < 2048, vw u.mem (scr s) o = shV V 0 1024 a j o) ?_
    ⟨m₄, by rw [r8, Nat.pow_zero, Nat.div_one], by rw [o₄.get .r9, e₃], by rw [k₄.mem]; exact Frame.refl _ _,
      fun o _ => by rw [k₄.mem]; rfl⟩ (by rw [e₄]))
    fun u ⟨mu, _, _, fu, vu⟩ => ⟨mu, fu, vu⟩
  intro j hj u ⟨mu, u8, u9, fu, vu⟩ _
  have hp9 : 2 ^ j ≤ 1024 := Nat.pow_le_pow_right (n := 2) (by decide) (show j ≤ 10 by omega_using [hj])
  refine WP.seq (WP.mono (pass_ok hp big mu u8 u9 hp9) fun u₁ ⟨m₁, k₁, f₁, v₁⟩ => ?_)
  refine wp_lsr fun u₂ p₂ f₂ => wp_add fun u₃ p₃ f₃ => wp_subi fun u₄ p₄ f₄ => wp_nil ?_
  have k₄' : Only [.r8, .r9, .r10] u₁ u₄ := (p₂.trans (p₃.trans p₄)).mono
  refine ⟨⟨m₁.step k₄'.keep (by decide) (Xs := []) (by rw [k₄'.mem]; exact Frame.refl _ _) (by simp), ?_, ?_,
    by rw [k₄'.mem]; exact fu.trans f₁, fun o ho => ?_⟩, ?_⟩
  · rw [p₄.get .r8, p₃.get .r8, f₂, k₁.get .r8, u8, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have hk := (s.gpr .r4).isLt
    have : a / 2 ^ j < 2 ^ 64 := by
      have := Nat.div_le_self a (2 ^ j); omega_using [this, hk]
    rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by have := Nat.div_le_self (a / 2 ^ j) 2; omega_arith)]
  · rw [p₄.get .r9, f₃, p₂.get .r9, k₁.get .r9, u9, ← BitVec.ofNat_add, Nat.pow_succ, Nat.mul_two]
  · rw [k₄'.mem, v₁ o ho]
    show passV (vw u.mem (scr s)) _ _ _ _ o = passV (shV V 0 1024 a j) _ _ _ _ o
    unfold passV
    by_cases c : 0 ≤ o ∧ o < 0 + 1024
    · rw [ifp c, ifp c, vu o ho, vu (o + 2 ^ j) (by omega_using [c, hp9])]
    · rw [ifn c, ifn c, vu o ho]
  · rw [f₄, p₃.get .r10, p₂.get .r10, k₁.get .r10]

end

/-! ## The message, first -/

theorem wordsAt_one (m : Mem) (p : Addr) : Spec.Rsa.wordsAt m p 1 = [m.readW p 64] := by
  simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero]

/-- What the callee leaves at `out` and `msg_len`: a message `M` after
zeros, and its length; and what the function must leave instead. -/
theorem shape {m : Mem} {out ml : Addr} {k : Nat} {r : BitVec 32} {o : Spec.Rsa.Outcome}
    (h : Proof.RsaPkcs1Enc.writtenMsg m out ml k r o) :
    ∃ M : List Byte, M.length ≤ k ∧ Spec.Rsa.bytesAt m out k = List.replicate (k - M.length) 0 ++ M ∧
      m.readW ml 64 = BitVec.ofNat 64 M.length ∧
      ∀ m' : Mem, Spec.Rsa.bytesAt m' out k = M ++ List.replicate (k - M.length) 0 →
        m'.readW ml 64 = m.readW ml 64 → Spec.RsaPkcs1Enc.writtenMsgFront m' out ml k r o := by
  cases o with
  | ok M =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    have hl := congrArg List.length hb
    rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, List.length_append, List.length_replicate] at hl
    refine ⟨M, by omega_arith, hb, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, hb', ?_⟩⟩
    rw [wordsAt_one, hw', List.cons.inj hw |>.1]
  | invalid =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    refine ⟨[], Nat.zero_le _, by rw [hb]; simp, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, ?_, ?_⟩⟩
    · rw [hb']; simp
    · rw [wordsAt_one, hw', List.cons.inj hw |>.1]
  | fault =>
    obtain ⟨hr, hb, hw⟩ := h
    rw [wordsAt_one] at hw
    refine ⟨[], Nat.zero_le _, by rw [hb]; simp, List.cons.inj hw |>.1, fun m' hb' hw' => ⟨hr, ?_, ?_⟩⟩
    · rw [hb']; simp
    · rw [wordsAt_one, hw', List.cons.inj hw |>.1]

theorem bytes_get {m : Mem} {p : Addr} {k : Nat} {T : List Byte} (hT : Spec.Rsa.bytesAt m p k = T) {i : Nat}
    (hi : i < k) : m (p + BitVec.ofNat 64 i) = T.getD i 0 := by
  rw [← hT]
  simp only [Spec.Rsa.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]

theorem getD_rep_app (a x : Nat) (M : List Byte) :
    (List.replicate a 0 ++ M).getD x 0 = if x < a then 0 else M.getD (x - a) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_replicate, List.getElem?_replicate]
  split <;> simp_all

/-- The buffer, shifted left by the zeros before the message: the message,
then zeros. -/
theorem shifted {m₀ m₁ m₂ m₃ m₄ : Mem} {out S : Addr} {k : Nat} {M : List Byte} (hML : M.length ≤ k)
    (hk : k ≤ 1024) (hk0 : k < 2 ^ 32) (hb : Spec.Rsa.bytesAt m₀ out k = List.replicate (k - M.length) 0 ++ M)
    (h₁ : m₁ = writeBytes m₀ S (List.replicate 2048 0)) (h₁' : Spec.Rsa.bytesAt m₁ out k = Spec.Rsa.bytesAt m₀ out k)
    (h₂ : m₂ = writeBytes m₁ S (Spec.Rsa.bytesAt m₁ out k))
    (h₃ : ∀ o < 2048, vw m₃ S o = shV (vw m₂ S) 0 1024 (k - M.length) 11 o)
    (h₄ : m₄ = writeBytes m₃ out (Spec.Rsa.bytesAt m₃ S k)) :
    Spec.Rsa.bytesAt m₄ out k = M ++ List.replicate (k - M.length) 0 := by
  have v₂ : ∀ x < 2048, vw m₂ S x = if x < k then (List.replicate (k - M.length) 0 ++ M).getD x 0 else 0 := by
    intro x hx
    rw [h₂, vw_wb _ _ _ (by omega_using [hx]), VG.Proof.RsaPkcs1Sig.bytesAt_length, h₁', hb, h₁,
      vw_wb _ _ _ (by omega_using [hx]), List.length_replicate, ifp hx]
    by_cases h : x < k
    · rw [ifp h, ifp h]
    · rw [ifn h, ifn h, List.getD_eq_getElem?_getD, List.getElem?_replicate, ifp hx]; rfl
  have hz : ∀ x, 1024 ≤ x → x < 1024 + 2 ^ 10 → vw m₂ S (0 + x) = 0 := fun x h1 h2 => by
    rw [Nat.zero_add, v₂ x (by omega_using [h2]), ifn (by omega_using [h1, hk])]
  have hlen : (Spec.Rsa.bytesAt m₄ out k).length = (M ++ List.replicate (k - M.length) 0).length := by
    simp only [VG.Proof.RsaPkcs1Sig.bytesAt_length, List.length_append, List.length_replicate]; omega_arith
  refine List.ext_getElem hlen fun i h1 h2 => ?_
  have hi : i < k := by rwa [VG.Proof.RsaPkcs1Sig.bytesAt_length] at h1
  have lhs : (Spec.Rsa.bytesAt m₄ out k)[i] = m₄ (out + BitVec.ofNat 64 i) := by
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  rw [lhs, h₄]
  simp only [writeBytes, Mem.sub_ofNat_toNat out (show i < 2 ^ 64 by omega_using [hi, hk]),
    VG.Proof.RsaPkcs1Sig.bytesAt_length, ifp hi]
  rw [← bytes_get (T := Spec.Rsa.bytesAt m₃ S k) rfl hi]
  have e := h₃ i (by omega_using [hi, hk])
  have e' := shV_in11 (vw m₂ S) 0 1024 (k - M.length) hz 11 (Nat.le_refl _) i (by omega_using [hi, hk])
  simp only [Nat.zero_add, Nat.mod_eq_of_lt (show k - M.length < 2 ^ 11 by omega_using [hk])] at e'
  rw [show m₃ (S + BitVec.ofNat 64 i) = vw m₃ S i from rfl, e, e']
  by_cases hm : i < M.length
  · rw [List.getElem_append_left hm, ifp (by omega_using [hm, hML, hk]), v₂ _ (by omega_using [hm, hML, hk]),
      ifp (by omega_using [hm, hML]), getD_rep_app, ifn (by omega_using []), Nat.add_sub_cancel,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
  · rw [List.getElem_append_right (by omega_using [hm]), List.getElem_replicate]
    by_cases h3 : i + (k - M.length) < 1024
    · rw [ifp h3, v₂ _ (by omega_using [h3]), ifn (by omega_using [hm, hML])]
    · rw [ifn h3]

/-! ## The function -/

/-- The function's postcondition, on the registers. -/
theorem front_post_of {s s' : State}
    (h : Spec.RsaPkcs1Enc.writtenMsgFront s'.mem (s.gpr .r3) (s.gpr .r5) (s.gpr .r7).toNat
      ((s'.gpr .r3).setWidth 32) (decOf s)) : FK.post s s' := by
  have e : fStack = 3919 + 1 := rfl
  show (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi fStack).post s s'
  rw [e]
  sig_post [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
    abi, argRegs, stackArgs_seventeen, List.append_eq]
  exact h

/-- The function, from a state its contract allows, meets its
postcondition. -/
theorem front_ok {c : Prog isa}
    (hv : ∀ s, K.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ K.post s s')
    (hd : sdepth c ≤ 3648) {name : String} {s : State} (hs : FK.pre s) :
    WP isa (Impl.RsaPkcs1Enc.PPC64LE.Front.code name c) s fun s' => abiPreserved s s' ∧ FK.post s s' := by
  obtain ⟨hp, hx, big⟩ := fpre_of hs
  have hk2 := hp.k2
  have h4 := hp.h4
  have wo := hp.wo
  have sl := scr_len hp
  refine WP.alloc (by decide) (by have := big.sp; unfold fStack at this; unfold frameBytes; omega_using [this]) ?_
  refine WP.seq (WP.mono (setup_ok hp big) fun t ht => ?_)
  refine WP.seq (WP.mono (call_ok hv hd hp hx big ht) fun t₂ hc => ?_)
  obtain ⟨M, hML, hb, hw, hfin⟩ := shape hc.post
  -- `out` and `msg_len` are apart from the buffer.
  have oS : ∀ {n : Nat}, n ≤ 2048 → (oR s).Disjoint ⟨scr s, n⟩ := fun h => hp.os.sub_right (scr_sub hp h)
  have mS : ∀ {n : Nat}, n ≤ 2048 → (mlR s).Disjoint ⟨scr s, n⟩ := fun h => hp.ms.sub_right (scr_sub hp h)
  have wbS : ∀ (m : Mem) (xs : List Byte), xs.length ≤ 2048 → Frame [⟨scr s, 2048⟩] m (writeBytes m (scr s) xs) :=
    fun m xs h => VG.WriteBytes.writeBytes_frame _ _ _ (Region.contains_self' h)
  refine WP.seq (WP.mono (after_ok hc) fun v₀ ⟨m₀, e₀⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (clear_ok hp big m₀) fun v₁ ⟨m₁, e₁⟩ => ?_))
  have f₁ : Frame [⟨scr s, 2048⟩] v₀.mem v₁.mem := by rw [e₁]; exact wbS _ _ (by rw [List.length_replicate])
  refine WP.seq (WP.mono (copyIn_ok hp big m₁) fun v₂ ⟨m₂, e₂⟩ => ?_)
  have f₂ : Frame [⟨scr s, 2048⟩] v₁.mem v₂.mem := by
    rw [e₂]; exact wbS _ _ (by rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; omega_using [hk2, h4])
  have hL : v₂.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 M.length := by
    rw [(f₁.trans f₂).readW (r := mlR s) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact mS (Nat.le_refl _)) (by decide), e₀]
    exact hw
  refine WP.seq (WP.mono (shift_ok hp big m₂ hL (by omega_using [hML, h4])) fun v₃ ⟨m₃, f₃, e₃⟩ => ?_)
  refine WP.mono (copyOut_ok hp big m₃) fun v₄ ⟨m₄, e₄⟩ => ?_
  refine WP.mono (restore_ok m₄) fun v₅ ⟨f₅, e₅⟩ m u hm => ?_
  rw [h4] at e₂ e₃ e₄
  have f₁' : Spec.Rsa.bytesAt v₁.mem (s.gpr .r3) (s.gpr .r7).toNat = Spec.Rsa.bytesAt v₀.mem (s.gpr .r3) (s.gpr .r7).toNat :=
    Proof.Rsa.rsa_bytes_frame f₁ (BitVec.isLt _) fun r hr => by
      rw [List.mem_singleton.mp hr, ← h4]; exact oS (Nat.le_refl _)
  have hout := shifted hML hk2 (by omega_using [hk2]) (by rw [e₀]; exact hb) e₁ f₁' e₂ e₃ e₄
  -- The frame, released.
  have fF : ∀ {R : Region}, (bigR s).Disjoint R → ∀ r ∈ [(⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ : Region)],
      R.Disjoint r := fun h r hr => by
    rw [List.mem_singleton.mp hr]; exact (h.sub_left (frame_big s)).symm
  have hm' : Frame [(⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩ : Region)] v₄.mem m := by rw [← e₅]; exact hm
  refine ⟨⟨fun r hr => f₅.g r hr, ?_, f₅.lr⟩, front_post_of ?_⟩
  · show v₅.sp + BitVec.ofNat 64 frameBytes = s.sp
    rw [f₅.sp, BitVec.sub_add_cancel]
  · show Spec.RsaPkcs1Enc.writtenMsgFront m _ _ _ ((v₅.gpr .r3).setWidth 32) _
    rw [f₅.r3]
    refine hfin m ?_ ?_
    · rw [Proof.Rsa.rsa_bytes_frame hm' (BitVec.isLt _) (fF (by rw [← h4]; exact big.ko)), hout]
    · have hall : Frame [⟨s.sp - BitVec.ofNat 64 frameBytes, frameBytes⟩, oR s, ⟨scr s, 2048⟩] v₀.mem m := by
        refine Frame.trans (Frame.sub (f₁.trans (f₂.trans (Frame.sub f₃ fun r hr => ?_))) fun r hr => ?_)
          (Frame.trans (Frame.sub (show Frame [oR s] v₃.mem v₄.mem by
            rw [e₄]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by
              rw [VG.Proof.RsaPkcs1Sig.bytesAt_length, ← h4]; exact Region.contains_self' (Nat.le_refl _)))
            fun r hr => ⟨r, by simp at hr ⊢; exact .inr (.inl hr), fun _ h => h⟩)
            (Frame.sub hm' fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩))
        · rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
        · rw [List.mem_singleton.mp hr]; exact ⟨_, by simp, fun _ h => h⟩
      rw [← e₀, hall.readW (r := mlR s) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact (big.km.sub_left (frame_big s)).symm
        · exact hp.om.symm
        · exact mS (Nat.le_refl _)) (by decide)]

/-! ## Constant time: the public data -/

/-- What both contracts may leak. -/
abbrev leakOf (x : State) : List Nat :=
  (Spec.Rsa.bytesAt x.mem (x.gpr .r6) (x.gpr .r7).toNat ++ Spec.Rsa.bytesAt x.mem (x.gpr .r8) (x.gpr .r9).toNat).map
    (·.toNat) ++ Spec.Rsa.privatePrecomputedLeak x.mem (stackArg x 15) (x.gpr .r7).toNat

theorem args17 {x₁ x₂ : State} (a0 : stackArg x₁ 0 = stackArg x₂ 0) (a1 : stackArg x₁ 1 = stackArg x₂ 1)
    (a2 : stackArg x₁ 2 = stackArg x₂ 2) (a3 : stackArg x₁ 3 = stackArg x₂ 3) (a4 : stackArg x₁ 4 = stackArg x₂ 4)
    (a5 : stackArg x₁ 5 = stackArg x₂ 5) (a6 : stackArg x₁ 6 = stackArg x₂ 6) (a7 : stackArg x₁ 7 = stackArg x₂ 7)
    (a8 : stackArg x₁ 8 = stackArg x₂ 8) (a9 : stackArg x₁ 9 = stackArg x₂ 9)
    (a10 : stackArg x₁ 10 = stackArg x₂ 10) (a11 : stackArg x₁ 11 = stackArg x₂ 11)
    (a12 : stackArg x₁ 12 = stackArg x₂ 12) (a13 : stackArg x₁ 13 = stackArg x₂ 13)
    (a14 : stackArg x₁ 14 = stackArg x₂ 14) (a15 : stackArg x₁ 15 = stackArg x₂ 15)
    (a16 : stackArg x₁ 16 = stackArg x₂ 16) : ∀ j < 17, stackArg x₁ j = stackArg x₂ j
  | 0, _ => a0 | 1, _ => a1 | 2, _ => a2 | 3, _ => a3 | 4, _ => a4 | 5, _ => a5 | 6, _ => a6 | 7, _ => a7
  | 8, _ => a8 | 9, _ => a9 | 10, _ => a10 | 11, _ => a11 | 12, _ => a12 | 13, _ => a13 | 14, _ => a14
  | 15, _ => a15 | 16, _ => a16 | _ + 17, h => absurd h (by omega_using [])

theorem regs8 {x₁ x₂ : State} (h3 : x₁.gpr .r3 = x₂.gpr .r3) (h4 : x₁.gpr .r4 = x₂.gpr .r4)
    (h5 : x₁.gpr .r5 = x₂.gpr .r5) (h6 : x₁.gpr .r6 = x₂.gpr .r6) (h7 : x₁.gpr .r7 = x₂.gpr .r7)
    (h8 : x₁.gpr .r8 = x₂.gpr .r8) (h9 : x₁.gpr .r9 = x₂.gpr .r9) (h10 : x₁.gpr .r10 = x₂.gpr .r10) :
    ∀ r ∈ argRegs, x₁.gpr r = x₂.gpr r := by
  intro r hr
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

/-- The function's public data: the stack pointer, the arguments and what
it may leak. -/
theorem front_pub {s₁ s₂ : State} (h : FK.pub s₁ s₂) :
    s₁.sp = s₂.sp ∧ (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ (∀ j < 17, stackArg s₁ j = stackArg s₂ j) ∧
      leakOf s₁ = leakOf s₂ := by
  have e : fStack = 3919 + 1 := rfl
  change (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi fStack).pub s₁ s₂ at h
  rw [e] at h
  sig_pub [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
    abi, argRegs, stackArgs_seventeen, List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨hsp, regs8 h3 h4 h5 h6 h7 h8 h9 h10, args17 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16, hl⟩

/-- `vg_rsa_pkcs1_decrypt_precomputed`'s public data. -/
theorem dec_pub_of {x₁ x₂ : State} (hsp : x₁.sp = x₂.sp) (hg : ∀ r ∈ argRegs, x₁.gpr r = x₂.gpr r)
    (ha : ∀ j < 17, stackArg x₁ j = stackArg x₂ j) (hl : leakOf x₁ = leakOf x₂) : K.pub x₁ x₂ := by
  have e : stackBytes = 3647 + 1 := rfl
  show (Proof.RsaPkcs1Enc.decryptPrecomputedContract abi stackBytes).pub x₁ x₂
  rw [e]
  sig_pub [Proof.RsaPkcs1Enc.decryptPrecomputedContract, Proof.RsaPkcs1Enc.decryptPrecomputedSig,
    Proof.RsaPkcs1Enc.decryptSig, abi, argRegs, stackArgs_seventeen, List.append_eq]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  exact ⟨hsp, hl, hg _ (by decide), hg _ (by decide), hg _ (by decide), hg _ (by decide), hg _ (by decide),
    hg _ (by decide), hg _ (by decide), hg _ (by decide), ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide), ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide), ha 16 (by decide)⟩

/-- What the callee may leak, at its entry: ours. -/
theorem leak_entry {s x : State} (hx : PreX s) (big : Big s)
    (hg : ∀ r ∈ argRegs, x.gpr r = s.gpr r) (ha : ∀ j < 17, stackArg x j = stackArg s j)
    (hm : Frame [⟨fb s, 272⟩] s.mem x.mem) : leakOf x = leakOf s := by
  have g6 := hg .r6 (by decide)
  have g7 := hg .r7 (by decide)
  have g8 := hg .r8 (by decide)
  have g9 := hg .r9 (by decide)
  have a15 := ha 15 (by decide)
  have hpl := hx.pl
  have kP : (bigR s).Disjoint ⟨stackArg s 15, Spec.Rsa.precomputedWords (s.gpr .r7).toNat * 8⟩ :=
    big.kP.sub_right (Region.sub_prefix (by
      rw [hpl]; unfold Spec.Rsa.privatePrecomputedWords; omega_arith))
  simp only [leakOf, Spec.Rsa.privatePrecomputedLeak, g6, g7, g8, g9, a15]
  rw [bytes_keep hm big.kn (BitVec.isLt _), bytes_keep hm big.ke (BitVec.isLt _), words_keep hm kP]

/-! ## Constant time -/

/-- The tail, from `Mid`. -/
theorem tail_mid {s v : State} {R : BitVec 64} (hp : DPre true s) (big : Big s) (h : Mid s R v) {L : Nat}
    (hL : v.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 L) (hLk : L ≤ (s.gpr .r4).toNat) :
    WP isa Impl.RsaPkcs1Enc.PPC64LE.Front.tail v (Mid s R) := by
  have hk2 := hp.k2
  have h4 := hp.h4
  have mS : (mlR s).Disjoint ⟨scr s, 2048⟩ := hp.ms.sub_right (scr_sub hp (Nat.le_refl _))
  refine WP.seq (WP.mono (clear_ok hp big h) fun v₁ ⟨m₁, e₁⟩ => ?_)
  refine WP.seq (WP.mono (copyIn_ok hp big m₁) fun v₂ ⟨m₂, e₂⟩ => ?_)
  have f : Frame [⟨scr s, 2048⟩] v.mem v₂.mem := by
    rw [e₂, e₁]
    exact (VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [List.length_replicate]; exact Region.contains_self' (Nat.le_refl _))).trans
      (VG.WriteBytes.writeBytes_frame _ _ _ (by
        rw [VG.Proof.RsaPkcs1Sig.bytesAt_length]; exact Region.contains_self' (by omega_using [hk2, h4])))
  have hL₂ : v₂.mem.readW (s.gpr .r5) 64 = BitVec.ofNat 64 L := by
    rw [f.readW (r := mlR s) (Region.contains_self _ _) (fun r hr => by rw [List.mem_singleton.mp hr]; exact mS)
      (by decide)]
    exact hL
  refine WP.seq (WP.mono (shift_ok hp big m₂ hL₂ hLk) fun v₃ ⟨m₃, _, _⟩ => ?_)
  exact WP.mono (copyOut_ok hp big m₃) fun v₄ ⟨m₄, _⟩ => m₄

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h' => hr r (Taint.mem_ofRegs.mp h')⟩) h

theorem setup_taint : ∃ hc, (taint.check (Taint.ofRegs []) (.block Impl.RsaPkcs1Enc.PPC64LE.Front.setup) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem after_taint : ∃ hc, (taint.check (Taint.ofRegs []) (.block Impl.RsaPkcs1Enc.PPC64LE.Front.after) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem tail_taint : ∃ hc, (taint.check (Taint.ofRegs [.r14, .r15, .r16, .r17]) Impl.RsaPkcs1Enc.PPC64LE.Front.tail hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem restore_taint : ∃ hc, (taint.check (Taint.ofRegs []) (.block Impl.RsaPkcs1Enc.PPC64LE.Front.restore) hc).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The function is constant time, given the callee's constant time. -/
theorem front_ct {c : Prog isa}
    (hv : ∀ s, K.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ K.post s s')
    (hct : ConstantTime isa K.pre K.pub c) (hd : sdepth c ≤ 3648) {name : String} :
    ConstantTime isa FK.pre FK.pub (Impl.RsaPkcs1Enc.PPC64LE.Front.code name c) := by
  refine RelCT.constantTime (RelCT.alloc (R := TT) (fun s₁ s₂ h => (front_pub h.2.2).1) ?_)
  intro a b ta tb a' b' ⟨σ₁, σ₂, ⟨h₁, h₂, hpub⟩, ea, eb⟩ e₁ e₂
  subst ea eb
  refine (?_ : RelCT isa (Eq2 (allocated frameBytes σ₁) (allocated frameBytes σ₂)) _ TT) _ _ _ _ _ _ ⟨rfl, rfl⟩
    e₁ e₂
  obtain ⟨hp₁, hx₁, big₁⟩ := fpre_of h₁
  obtain ⟨hp₂, hx₂, big₂⟩ := fpre_of h₂
  obtain ⟨_, st⟩ := setup_taint
  obtain ⟨_, at'⟩ := after_taint
  obtain ⟨_, tt⟩ := tail_taint
  obtain ⟨_, rt⟩ := restore_taint
  obtain ⟨hsp, hg, ha, hl⟩ := front_pub hpub
  have hfb : fb σ₁ = fb σ₂ := by rw [fb, fb, hsp]
  refine rel_seq (rel_taint [] hfb (by simp) st) (setup_ok hp₁ big₁) (setup_ok hp₂ big₂)
    fun t₁ t₂ ht₁ ht₂ => ?_
  refine rel_seq (RelCT.callEx hv hct fun x y ⟨ex, ey⟩ => ?_) (call_ok hv hd hp₁ hx₁ big₁ ht₁)
    (call_ok hv hd hp₂ hx₂ big₂ ht₂) fun u₁ u₂ hc₁ hc₂ => ?_
  · subst ex ey
    obtain ⟨esp₁, eg₁, ea₁, em₁⟩ := entry_facts ht₁
    obtain ⟨esp₂, eg₂, ea₂, em₂⟩ := entry_facts ht₂
    have hm₁ : Frame [⟨fb σ₁, 272⟩] σ₁.mem (entry σ₁ x).mem := by rw [em₁]; exact ht₁.fr
    have hm₂ : Frame [⟨fb σ₂, 272⟩] σ₂.mem (entry σ₂ y).mem := by rw [em₂]; exact ht₂.fr
    obtain ⟨c₁, w₁⟩ := entry_covers hp₁ ht₁
    obtain ⟨c₂, w₂⟩ := entry_covers hp₂ ht₂
    refine ⟨RD σ₁, WR σ₁, RD σ₂, WR σ₂, dec_pre_of (dpre_entry hp₁ big₁ esp₁ eg₁ ea₁ rfl rfl)
      (prex_entry hx₁ big₁ esp₁ eg₁ ea₁ hm₁), dec_pre_of (dpre_entry hp₂ big₂ esp₂ eg₂ ea₂ rfl rfl)
      (prex_entry hx₂ big₂ esp₂ eg₂ ea₂ hm₂), dec_pub_of (by rw [esp₁, esp₂, hfb])
      (fun r hr => by rw [eg₁ r hr, eg₂ r hr, hg r hr]) (fun j hj => by rw [ea₁ j hj, ea₂ j hj, ha j hj])
      ((leak_entry hx₁ big₁ eg₁ ea₁ hm₁).trans (hl.trans (leak_entry hx₂ big₂ eg₂ ea₂ hm₂).symm)), c₁, w₁, c₂,
      w₂⟩
  refine rel_seq (rel_taint [] (by rw [hc₁.sp, hc₂.sp, hfb]) (by simp) at') (after_ok hc₁) (after_ok hc₂)
    fun v₁ v₂ ⟨m₁, e₁⟩ ⟨m₂, e₂⟩ => ?_
  obtain ⟨M₁, hML₁, -, hw₁, -⟩ := shape hc₁.post
  obtain ⟨M₂, hML₂, -, hw₂, -⟩ := shape hc₂.post
  have h4₁ := hp₁.h4
  have h4₂ := hp₂.h4
  refine rel_seq (rel_taint [.r14, .r15, .r16, .r17] (by rw [m₁.sp, m₂.sp, hfb]) (fun r hr => ?_) tt)
    (tail_mid hp₁ big₁ m₁ (by rw [e₁]; exact hw₁) (by omega_using [hML₁, h4₁]))
    (tail_mid hp₂ big₂ m₂ (by rw [e₂]; exact hw₂) (by omega_using [hML₂, h4₂])) fun w₁ w₂ n₁ n₂ => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [m₁.g14, m₂.g14, hg _ (by decide)]
    · rw [m₁.g15, m₂.g15, hg _ (by decide)]
    · rw [m₁.g16, m₂.g16, hg _ (by decide)]
    · rw [m₁.g17, m₂.g17, scr, scr, ha 13 (by decide)]
  exact rel_taint [] (by rw [n₁.sp, n₂.sp, hfb]) (by simp) rt

/-! ## `Verified` -/

/-- The precondition, from the facts of a state (as `Dec.pre_of_facts`). -/
theorem pre_of_factsF {s : State} (hg : s.gpr = Dec.satP.gpr) (hsp : s.sp = 0x10000)
    (ha : ∀ j < 17, stackArg s j = Dec.satArgs j) (hrd : s.rd = Dec.satP.rd) (hwr : s.wr = Dec.satP.wr)
    (hk : Spec.Rsa.privatePrecompute (Spec.Rsa.bytesAt s.mem 0x2000 64) (Spec.Rsa.bytesAt s.mem 0x4200 32)
      (Spec.Rsa.bytesAt s.mem 0x4300 32) = some (Spec.Rsa.wordsAt s.mem 0x4800 24)) : FK.pre s := by
  have e : fStack = 3919 + 1 := rfl
  show (Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract abi fStack).pre s
  rw [e]
  sig_pre [Spec.RsaPkcs1Enc.decryptPrecomputedFrontContract, Spec.RsaPkcs1Enc.decryptPrecomputedFrontSig,
    abi, argRegs, List.append_eq, List.range, List.range.loop]
  have hA : ∀ j, stackArgAddr s j = 0x10000 + BitVec.ofNat 64 (32 + 8 * (8 + j)) := fun j => by
    simp only [stackArgAddr, hsp]
  simp only [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),
    ha 5 (by decide), ha 6 (by decide), ha 7 (by decide), ha 8 (by decide), ha 9 (by decide), ha 10 (by decide),
    ha 11 (by decide), ha 12 (by decide), ha 13 (by decide), ha 14 (by decide), ha 15 (by decide),
    ha 16 (by decide), hg, hsp, hrd, hwr, hA, Dec.satArgs, Dec.satP]
  simp only [Nat.reduceEqDiff, ↓reduceIte, or_self, or_false, false_or]
  sig_and_intros
  all_goals first
    | exact hk
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (simp only [Spec.Rsa.lenValid]; decide)

/-- A state that meets the contract: `vg_rsa_pkcs1_decrypt_precomputed`'s
(`Dec.satP`). -/
theorem satF : ∃ s, FK.pre s :=
  ⟨Dec.satP, pre_of_factsF rfl rfl Dec.satP_args rfl rfl
    (Proof.Rsa.PreKey.key_pre_of fun _ ha => Dec.satP_key ha)⟩

/-- `vg_rsa_pkcs1_decrypt_precomputed_front` on PPC64LE, calling code
verified as `vg_rsa_pkcs1_decrypt_precomputed` with 3648 bytes of stack,
meets its contract with 3920. -/
theorem front_verified {name : String} {c : Prog isa} (h : Verified target c K) (hd : sdepth c ≤ 3648) :
    Verified target (Impl.RsaPkcs1Enc.PPC64LE.Front.code name c) FK := by
  obtain ⟨hv, hct, -⟩ := h
  refine ⟨fun s hs => ?_, front_ct hv hct hd, satF⟩
  obtain ⟨t, s', he, ha, hq⟩ := front_ok hv hd (name := name) hs
  exact ⟨t, s', he, ha, hq⟩

end VG.Proof.RsaPkcs1Enc.PPC64LE.Front
