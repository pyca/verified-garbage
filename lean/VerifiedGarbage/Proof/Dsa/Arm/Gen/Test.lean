module

public import VerifiedGarbage.Impl.Dsa.Arm.ProbablePrime
public import VerifiedGarbage.Proof.Dsa.ProbablePrimeContract
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Generation.Memory
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.St
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.Arm.Gen.Bytes
public import VerifiedGarbage.Proof.Dsa.Arm.Gen.Frame
import VerifiedGarbage.Proof.Framework.ReadHalves
import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
import VerifiedGarbage.Proof.Dsa.Generation.RandomSuffix
public import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
import VerifiedGarbage.Proof.Bignum.Arm.CopyBuffer
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! ### `Dsa.Arm.Gen.Tape`, which this module and modules that import it used -/

section

/-! # DSA parameter generation on ARMv7: copies from the tapes

`copyR_vp`: `n` bytes from an address a frame word holds (a seed, an `h`)
into `scratch`. `GI.tapeBytes`: the tapes keep their bytes through the
search, which writes only the frame, `scratch` and the stack below.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_movw wp_mov wp_dp op2_reg op2_imm dpVal)
open VG.Proof.Rsa.Arm.Recover (VP)

section
variable {G : GP}

theorem copyBytes_cert :
    ∃ hc, (VG.Taint.check VG.Arm.taint (Taint.ofRegs [.r0, .r1, .lr]) VG.Impl.Bignum.Arm.copyBytes hc).isSome = true :=
  ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0, .r1, .lr]) VG.Impl.Bignum.Arm.copyBytes, by kernel_rfl⟩

/-- A copy by `copyBytes`, from `src` to `dst`, with its pointers and length known. -/
theorem copyBytes_vp {P Q : State → State → Prop} {src dst : BitVec 32} {n : Nat}
    (hp : ∀ σ s, P σ s → s.gpr .r1 = src ∧ s.gpr .r0 = dst ∧ s.gpr .lr = BitVec.ofNat 32 n)
    (wp : ∀ σ s, P σ s → WP isa VG.Impl.Bignum.Arm.copyBytes s (Q σ)) :
    VP P VG.Impl.Bignum.Arm.copyBytes Q :=
  VP.taint [.r0, .r1, .lr] copyBytes_cert (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
    obtain ⟨a₁, b₁, c₁⟩ := hp _ _ h₁
    obtain ⟨a₂, b₂, c₂⟩ := hp _ _ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [b₁, b₂]
    · rw [a₁, a₂]
    · rw [c₁, c₂]) wp

/-- `n` bytes from the address `x` in the frame word `o`, readable and apart
from `scratch`, to `scratch + dst`. -/
theorem copyR_vp {P Q : State → State → Prop} {c : State → Cfg} {L dst n o : Nat} {x : BitVec 32}
    (hF : ∀ σ s, P σ s → SS G σ (c σ) s) (hL : L = G.pLen) (ho : o + 4 ≤ F + 16) (h4 : o % 4 = 0)
    (hx : ∀ σ s, P σ s → fw s.mem G o = x) (hn : 0 < n) (hn16 : n < 2 ^ 16) (hd : dst + n ≤ sK L)
    (hsrc : ∀ σ s, P σ s → InRegions s.rd (State.addr x) n ∧ Region.Disjoint ⟨State.addr x, n⟩ G.rScr ∧
      x.toNat + n ≤ 2 ^ 32)
    (k : ∀ σ s t, P σ s → Rest [.r0, .r1, .r2, .r12, .lr] s t → Frame [G.rs dst n] s.mem t.mem →
      Spec.Rsa.bytesAt t.mem (G.sa dst) n = Spec.Rsa.bytesAt s.mem (State.addr x) n → Q σ t) :
    VP P (copyN (scr L .r0 dst) [ld .r1 o] n) Q := by
  -- After the pointers and the count.
  let P₂ : State → State → Prop := fun σ t => ∃ s, P σ s ∧ Rest [.r0, .r1, .r12, .lr] s t ∧ t.mem = s.mem ∧
    t.gpr .r1 = x ∧ t.gpr .r0 = G.scr + BitVec.ofNat 32 dst ∧ t.gpr .lr = BitVec.ofNat 32 n
  simp only [copyN, List.append_assoc]
  refine VP.seq (G := P₂) (VP.block_append (G := fun σ t => ∃ s, P σ s ∧ Upd s t .r1 x)
    (ld_vp hF ho h4 hx fun σ s t hs u => ⟨s, hs, u⟩) ?_) ?_
  · refine VP.taint [.r1, .r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1, .r8])
        (.block (scr 128 .r0 0 ++ [.movw .lr (BitVec.ofNat 16 5)])), by kernel_rfl⟩
      (fun σ₁ σ₂ s₁ s₂ ⟨_, h₁, u₁⟩ ⟨_, h₂, u₂⟩ r hr => ?_) fun σ t ⟨s, hs, u⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [u₁.gpr, u₂.gpr]
      · rw [u₁.other _ (by decide), u₂.other _ (by decide), (hF _ _ h₁).r8, (hF _ _ h₂).r8]
    have h := hF σ s hs
    have big := h.gi.scrBig
    subst hL
    refine scr_ok (d := .r0) (by rw [u.other _ (by decide)]; exact h.r8) rfl h.lens (by omega_using [hd])
      fun s₁ v₁ R₁ M₁ => wp_movw fun s₂ u₂ => WP.block_nil
        ⟨s, hs, ((u.rest (by simp)).trans (R₁.mono (by simp))).trans (u₂.rest (by simp)),
          by rw [u₂.mem, M₁, u.mem], by rw [u₂.other _ (by decide), R₁.gpr _ (by decide), u.gpr],
          by rw [u₂.other _ (by decide)]; exact v₁, ?_⟩
    rw [u₂.gpr]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega_using [hn16]
  refine copyBytes_vp (src := x) (dst := G.scr + BitVec.ofNat 32 dst) (n := n)
    (fun σ t ⟨_, _, _, _, a, b, c⟩ => ⟨a, b, c⟩) fun σ s₂ ⟨s, hs, R, M, v1, v0, vl⟩ => ?_
  have h := hF σ s hs
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  obtain ⟨rd, dj, xf⟩ := hsrc σ s hs
  subst hL
  have ad := h.addr hd hn
  refine WP.mono (VG.Proof.Bignum.Arm.copyBuffer_ok s₂ (src := x) (dst := G.scr + BitVec.ofNat 32 dst) hn xf
    (by rw [h.toNat (by omega_using [hd])]; omega_using [big, fit, hd]) (by omega_using [hn16])
    (by rw [R.rd]; obtain ⟨r, hr, hc⟩ := rd; exact ⟨r, List.mem_append_left _ hr, hc⟩)
    (by rw [ad, R.wr]; exact gi.inScr (by omega_using [big, hd]))
    (by rw [ad]; exact dj.sub_right (sw G (by omega_using [big, hd]))) v0 v1 vl)
    fun t' ⟨rd', fr, _, rest⟩ => k σ s t' hs ((R.mono (by simp)).trans (rest.mono (by simp)))
      (by rw [← M]; show Frame [⟨G.sa dst, n⟩] _ _; rw [← ad]; exact fr) ?_
  rw [← ad, ← M]; exact bytesAt_of_read rd'

/-- A slice of bytes. -/
theorem bytesAt_slice' (m : Mem) (p : Addr) {k n len : Nat} (h : k + n ≤ len) :
    Spec.Rsa.bytesAt m (p + BitVec.ofNat 64 k) n = ((Spec.Rsa.bytesAt m p len).drop k).take n := by
  obtain ⟨r, rfl⟩ : ∃ r, len = k + (n + r) := ⟨len - k - n, by omega_using [h]⟩
  rw [VG.Proof.Dsa.Generation.bytesAt_append, VG.Proof.Dsa.Generation.bytesAt_append,
    List.drop_left' (bytesAt_length' _ _ _),
    List.take_left' (bytesAt_length' _ _ _)]

/-- A range the search does not write keeps its bytes. -/
theorem GI.keeps {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) {p : BitVec 32}
    {len : Nat} (hfit : p.toNat + len ≤ 2 ^ 32) (hd : ∀ r ∈ G.chg, Region.Disjoint ⟨State.addr p, len⟩ r) {k n : Nat}
    (hk : k + n ≤ len) :
    Spec.Rsa.bytesAt s.mem (State.addr (p + BitVec.ofNat 32 k)) n =
      ((Spec.Rsa.bytesAt σ.mem (State.addr p) len).drop k).take n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Spec.Rsa.bytesAt]
  rw [addr_add (by omega_using [hfit, hk, hn]), ← bytesAt_slice' σ.mem _ hk]
  exact VG.Proof.Dsa.Generation.frame_bytesAt h.frame (fun r hr => (hd r hr).sub_left
    (Offset.sub_base _ (by omega_using [hk]))) (by omega_using [hfit, hk])

/-- The tapes are apart from what the search writes. -/
theorem GI.tape_apart {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) {R : Region}
    (hst : R.Disjoint (rStack σ)) (hsc : R.Disjoint G.rScr) : ∀ r ∈ G.chg, R.Disjoint r := fun r hr => by
  simp only [GP.chg, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hst.sub_right h.frameSub
  · exact hsc
  · exact hst.sub_right h.belowSub

theorem GI.wit_apart {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) :
    ∀ r ∈ G.chg, G.rWit.Disjoint r := by
  have a := h.pre.fW; have b := h.pre.wC; rw [h.hG] at a b
  exact h.tape_apart a.symm b

theorem GI.seeds_apart {σ s : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS s) :
    ∀ r ∈ G.chg, G.rSeeds.Disjoint r := h.wit_apart

end

end VG.Proof.Dsa.Arm.Gen

end

end

/-! ### `Dsa.Arm.Gen.PrimeCall`, which only this module used -/

section

/-! ### `Dsa.Arm.Gen.PrimeIface`, which only this module used -/

section

/-! # DSA's probable-prime test on ARMv7, as its callers see it

The contract of `vg_dsa_probable_prime` (`Proof.Dsa.ProbablePrime.sizedContract`
for the ARMv7 layout and sizes, 144 bytes of stack) for a size `bits` in plain
facts: its precondition (`PIn`, `pre_of_pin`), its postcondition (`PPost`,
`ppost_of_post`) and what two calls must agree on (`pub_of`).
`PrimeOk bits code`: a verified test, and `bits` one of its sizes.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout sizes)

/-- The test's contract. -/
abbrev primeK : Contract isa := Proof.Dsa.ProbablePrime.sizedContract layout sizes abi 144

/-- A verified test, with the stack it uses, for a size it takes. -/
structure PrimeOk (bits : Nat) (code : Prog isa) : Prop where
  verified : Verified target code primeK
  stack : FrameStack.armStack code ≤ 144
  sized : bits ∈ sizes

/-- The candidate at `ws`. -/
abbrev candOf (bits : Nat) (s : State) : Nat :=
  Proof.Dsa.ProbablePrime.candidateAt (layout bits) s.mem (State.addr (s.gpr .r0))

/-- The precondition, as facts. -/
structure PIn (bits : Nat) (s : State) : Prop where
  sized : bits ∈ sizes
  arg : stackArg s 1 = BitVec.ofNat 32 bits
  spLo : 144 ≤ s.sp.toNat
  spHi : s.sp.toNat + 8 ≤ 2 ^ 32
  rd : s.rd = [⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩, ⟨stackArgAddr s 0, 8⟩]
  wr : s.wr = [⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩, ⟨State.addr (stackArg s 0), 8⟩]
  wR : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  wU : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨State.addr (stackArg s 0), 8⟩
  wA : Region.Disjoint ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩ ⟨stackArgAddr s 0, 8⟩
  rU : Region.Disjoint ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩ ⟨State.addr (stackArg s 0), 8⟩
  uA : Region.Disjoint ⟨State.addr (stackArg s 0), 8⟩ ⟨stackArgAddr s 0, 8⟩
  FW : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat * 8⟩
  FR : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  FU : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨State.addr (stackArg s 0), 8⟩
  FA : Region.Disjoint ⟨State.addr s.sp - 144#64, 144⟩ ⟨stackArgAddr s 0, 8⟩
  fw : (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32
  fr : (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32
  fu : (stackArg s 0).toNat + 8 ≤ 2 ^ 32
  size : keyOff + 8 * keyWords bits ≤ 8 * (s.gpr .r1).toNat
  odd : candOf bits s % 2 = 1
  bl : Spec.Dsa.bitLength (candOf bits s) = bits

/-- The size, from the second stack argument. -/
theorem PIn.bits {bits : Nat} {s : State} (h : PIn bits s) : (stackArg s 1).toNat = bits := by
  rw [h.arg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := h.sized; simp only [sizes, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

theorem pre_of_pin {bits : Nat} {s : State} (h : PIn bits s) : primeK.pre s := by
  sig_pre [primeK, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs,
    reduceClassify, Loc.val]
  rw [h.bits]
  exact ⟨h.spLo, h.spHi, h.rd, h.wr, h.wR, h.wU, h.wA, h.rU, h.uA, h.FW, h.FR, h.FU, h.FA, h.fw, h.fr, h.fu, h.sized,
    h.size, h.odd, h.bl⟩

/-- The test's result. -/
abbrev resOf (bits : Nat) (s : State) : Option (Bool × Spec.RsaKeyGen.Rand) :=
  Spec.Dsa.probablePrime (candOf bits s) (Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)

/-- The postcondition, as facts. -/
def PPost (bits : Nat) (s t : State) : Prop :=
  (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status (resOf bits s) ∧
    Proof.Dsa.ModPow.Keeps (State.addr (s.gpr .r0)) (s.gpr .r1).toNat [(keyOff, 8 * keyWords bits)] s.mem t.mem ∧
    ∀ b rest, resOf bits s = some (b, rest) →
      Spec.Rsa.wordsAt t.mem (State.addr (stackArg s 0)) 1 = [BitVec.ofNat 64 ((s.gpr .r3).toNat - rest.length)]

theorem ppost_of_post {bits : Nat} {s t : State} (hb : (stackArg s 1).toNat = bits) (h : primeK.post s t) :
    PPost bits s t := by
  sig_post [primeK, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr] at h
  rw [BitVec.setWidth_append_eq_right, hb] at h
  exact h

/-- Two calls with the same public arguments, candidate and tape. -/
theorem pub_of {bits : Nat} {s t : State} (sp : s.sp = t.sp) (p0 : s.gpr .r0 = t.gpr .r0)
    (p1 : s.gpr .r1 = t.gpr .r1) (p2 : s.gpr .r2 = t.gpr .r2) (p3 : s.gpr .r3 = t.gpr .r3)
    (a0 : stackArg s 0 = stackArg t 0) (a1 : stackArg s 1 = stackArg t 1) (hb : (stackArg s 1).toNat = bits)
    (hc : candOf bits s = candOf bits t)
    (hr : Spec.Rsa.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Rsa.bytesAt t.mem (State.addr (t.gpr .r2)) (t.gpr .r3).toNat) :
    primeK.pub s t := by
  sig_pub [primeK, Proof.Dsa.ProbablePrime.sizedContract, Proof.Dsa.ProbablePrime.sizedSig, abi, argRegs,
    reduceClassify, Loc.val, State.addr]
  rw [← a1, hb]
  exact ⟨sp, by simp only [candOf, State.addr] at hc hr; rw [hc, hr], p0, p1, p2, p3, a0, rfl⟩

end VG.Proof.Dsa.Arm.Gen

end

end


/-! # DSA parameter generation on ARMv7: calling the probable-prime test

`primeCall_vp`: `callWith name code`, its stack arguments (the count's
address, in `r4`, and the size, in `r5`) pushed, calls the test on the
candidate at `sA` with the witnesses from `u` on: its status in `r0`, its count in the frame word
`fUsedOut` when the tape sufficed, and `scratch` changed only from `sA` to the
key working space.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)
open VG.Proof.X25519.Arm (Rest Upd Mupd)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Arm.FrameStack (armStack belowA)

/-- The words a call pushes. -/
abbrev callPush : List Reg := [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- A push's first word is its first register. -/
theorem pushed_arg0 {s : State} {r : Reg} {rs : List Reg} (h : 4 * (rs.length + 1) ≤ s.sp.toNat) :
    stackArg (pushed (r :: rs) s) 0 = s.gpr r := by
  obtain hs := FrameStack.sub_toNat' h
  have := s.sp.isLt
  simp only [stackArg, stackArgAddr, pushed, List.map_cons, storeWords, Nat.mul_zero, BitVec.add_zero,
    List.length_cons]
  generalize s.sp - BitVec.ofNat 32 (4 * (rs.length + 1)) = a at hs ⊢
  obtain ha : a.toNat + 4 * (rs.length + 1) ≤ 2 ^ 32 := by rw [hs]; omega_arith
  obtain h4 : (a + 4).toNat = a.toNat + 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  rw [(FrameStack.storeWords_frame (rs.map s.gpr) _ (a + 4) (by rw [h4, List.length_map]; omega_arith)).readW
    (r := ⟨State.addr a, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add (by omega_arith)]
      exact (Offset.disjoint_base _ (Nat.le_refl 4) (by
        have := VG.Proof.X25519.Arm.addr_toNat a; rw [List.length_map]; omega_arith)).symm)
    (by decide), Mem.readW_writeW_self32]

/-- A push's word at `b` is its first register. -/
theorem storeWords_head (m : Mem) (b v : BitVec 32) (vs : List (BitVec 32))
    (h : b.toNat + 4 * (vs.length + 1) < 2 ^ 32) : (storeWords m b (v :: vs)).readW (State.addr b) 32 = v := by
  obtain h4 : (b + 4).toNat = b.toNat + 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  rw [storeWords, (FrameStack.storeWords_frame vs _ (b + 4) (by rw [h4]; omega_arith)).readW
    (r := ⟨State.addr b, 4⟩) (Region.contains_self _ _) (fun r' hr' => by
      simp only [List.mem_singleton] at hr'; subst hr'
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, VG.Arm.addr_add (by omega_arith)]
      exact (Offset.disjoint_base _ (Nat.le_refl 4) (by
        have := VG.Proof.X25519.Arm.addr_toNat b; omega_arith)).symm)
    (by decide), Mem.readW_writeW_self32]

/-- A push's second word is its second register. -/
theorem pushed_arg1 {s : State} {r r' : Reg} {rs : List Reg} (h : 4 * (rs.length + 2) ≤ s.sp.toNat) :
    stackArg (pushed (r :: r' :: rs) s) 1 = s.gpr r' := by
  obtain hs := FrameStack.sub_toNat' h
  have := s.sp.isLt
  show (storeWords ((s.mem).writeW (State.addr (s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)))) (s.gpr r))
    (s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)) + 4) (s.gpr r' :: rs.map s.gpr)).readW
    (State.addr (s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)) + 4)) 32 = _
  generalize s.sp - BitVec.ofNat 32 (4 * (rs.length + 2)) = a at hs ⊢
  obtain ha : a.toNat + 4 * (rs.length + 2) < 2 ^ 32 := by rw [hs]; omega_arith
  obtain h4 : (a + 4).toNat = a.toNat + 4 := by
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := 4) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  exact storeWords_head _ _ _ _ (by rw [h4, List.length_map]; omega_arith)

section
variable {G : GP} {σ s : State} {V : Nat → BitVec 32} {LS : List Nat}

theorem GI.sp176 (h : GI G σ V LS s) : 176 ≤ G.sp.toNat := by
  have := h.spN; have := h.pre.spLo; simp only [F] at *; omega_arith

/-- Where the witnesses from `u` on start: `witnesses` itself when none is left. -/
abbrev GP.randP (G : GP) (u : Nat) : BitVec 32 := if u = G.witLen then G.wit else G.wit + BitVec.ofNat 32 u

/-- The witnesses from `u` on. -/
abbrev GP.rRand (G : GP) (u : Nat) : Region :=
  ⟨State.addr (G.randP u), (BitVec.ofNat 32 (G.witLen - u)).toNat⟩

theorem GI.witFit (h : GI G σ V LS s) : G.wit.toNat + G.witLen ≤ 2 ^ 32 := by
  have := h.pre.nW; rw [← h.hG]; exact this

theorem GI.witLt (h : GI G σ V LS s) : G.witLen < 2 ^ 32 := by
  rw [← h.hG]; exact (stackArg σ 0).isLt

theorem GI.randLen (h : GI G σ V LS s) (u : Nat) : (BitVec.ofNat 32 (G.witLen - u)).toNat = G.witLen - u := by
  have := h.witLt; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith)]

theorem GI.randAddr (h : GI G σ V LS s) {u : Nat} (hu : u < G.witLen) :
    State.addr (G.randP u) = State.addr G.wit + BitVec.ofNat 64 u := by
  have := h.witFit
  rw [GP.randP, ite_eq_right (by omega_arith)]; exact addr_add (by omega_arith)

/-- The witnesses from `u` on are within the tape. -/
theorem GI.randIn (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : G.rWit.Contains (State.addr (G.randP u))
    (BitVec.ofNat 32 (G.witLen - u)).toNat := by
  have := h.witFit
  rw [h.randLen]
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [h.randAddr hl]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · rw [GP.randP, ite_eq_left (by omega_arith), show G.witLen - u = 0 by omega_arith]
    show (_ - _ : Addr).toNat + 0 ≤ G.witLen
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega_arith

theorem GI.randSub (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) : Region.Sub (G.rRand u) G.rWit := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · show Region.Sub ⟨_, _⟩ _
    rw [h.randLen, h.randAddr hl]; exact Offset.sub_base _ (by omega_arith)
  · show Region.Sub ⟨_, _⟩ _
    rw [h.randLen, show G.witLen - u = 0 by omega_arith]
    intro a ha; simp [Region.Contains] at ha

theorem GI.randFit (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    (G.randP u).toNat + (G.witLen - u) ≤ 2 ^ 32 := by
  have := h.witFit
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega_arith), BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := u) (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · have := (G.randP u).isLt; omega_arith

/-- The witnesses from `u` on, in memory. -/
theorem GI.randBytes (h : GI G σ V LS s) {u : Nat} (hu : u ≤ G.witLen) :
    Spec.Rsa.bytesAt s.mem (State.addr (G.randP u)) (G.witLen - u) = G.witB.drop u := by
  obtain wl : G.witB.length = G.witLen := by rw [← h.hG]; exact bytesAt_length' _ _ _
  rcases Nat.lt_or_ge u G.witLen with hl | hl
  · rw [GP.randP, ite_eq_right (by omega_arith), h.keeps h.witFit (fun r hr => h.wit_apart r hr) (k := u) (n := G.witLen - u)
      (by omega_arith)]
    rw [show Spec.Rsa.bytesAt σ.mem (State.addr G.wit) G.witLen = G.witB by rw [← h.hG]; rfl,
      List.take_of_length_le (by rw [List.length_drop]; omega_arith)]
  · rw [show G.witLen - u = 0 by omega_arith, List.drop_of_length_le (by omega_arith)]; rfl

/-- The stack the call uses, below the frame: the pushed words and the test's 144 bytes. -/
theorem GI.pushSub (h : GI G σ V LS s) :
    Region.Sub (belowA G.sp 32) G.rBelow := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32), 32⟩ ⟨State.addr G.sp - 176#64, 176⟩
  rw [FrameStack.addr_sub' (by omega_arith)]
  exact Offset.sub_below _ (by omega_arith) (by omega_arith)

theorem GI.testSub (h : GI G σ V LS s) :
    Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length)) - 144#64, 144⟩ G.rBelow := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32) - BitVec.ofNat 64 144, 144⟩ ⟨State.addr G.sp - 176#64, 176⟩
  rw [FrameStack.addr_sub' (by omega_arith), BitVec.sub_sub, ← BitVec.ofNat_add]
  exact Offset.sub_below _ (by omega_arith) (by omega_arith)

theorem GI.argSub (h : GI G σ V LS s) :
    Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 8⟩
      (belowA G.sp 32) := by
  have := h.sp176
  show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 32 + 0#32), 8⟩ ⟨State.addr (G.sp - BitVec.ofNat 32 32), 32⟩
  rw [BitVec.add_zero]; exact fun _ h => by simp only [Region.Contains] at h ⊢; omega_arith

/-- The count's 8 bytes. -/
theorem GI.usedAddr (h : GI G σ V LS s) :
    State.addr (G.sp + BitVec.ofNat 32 fUsedOut) = State.addr G.sp + BitVec.ofNat 64 fUsedOut := by
  have := h.spHi; exact addr_add (by simp only [fUsedOut, F] at *; omega_arith)

/-- The test's arguments, in `r0`–`r5`. -/
abbrev TArgs (G : GP) (L u bits : Nat) (s : State) : Prop :=
  s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r1 = BitVec.ofNat 32 (wa L / 8) ∧
  s.gpr .r2 = G.randP u ∧ s.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) ∧
  s.gpr .r4 = G.sp + BitVec.ofNat 32 fUsedOut ∧ s.gpr .r5 = BitVec.ofNat 32 bits

/-- The regions the test is given. -/
abbrev tRd (G : GP) (u : Nat) : List Region :=
  [G.rRand u, ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 8⟩]
abbrev tWr (G : GP) (L : Nat) : List Region :=
  [⟨State.addr (G.scr + BitVec.ofNat 32 sA), (BitVec.ofNat 32 (wa L / 8)).toNat * 8⟩,
    ⟨State.addr (G.sp + BitVec.ofNat 32 fUsedOut), 8⟩]

/-- The test's entry. -/
abbrev tEntry (G : GP) (L u : Nat) (s : State) : State := (pushed callPush s).callEntry.withRegions (tRd G u) (tWr G L)

theorem wa_toNat {L : Nat} (hL : L = 128 ∨ L = 256 ∨ L = 384) : (BitVec.ofNat 32 (wa L / 8)).toNat * 8 = wa L := by
  simp only [wa]; rcases hL with rfl | rfl | rfl <;> decide

theorem tEntry_gpr {G : GP} {L u : Nat} {s : State} {r : Reg} (hr : r ∉ linkRegs) :
    (tEntry G L u s).gpr r = s.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ hr, pushed_gpr]

theorem tEntry_sp {G : GP} {L u : Nat} {s : State} :
    (tEntry G L u s).sp = s.sp - BitVec.ofNat 32 (4 * callPush.length) := rfl

theorem tEntry_mem {G : GP} {L u : Nat} {s : State} : (tEntry G L u s).mem = (pushed callPush s).mem := rfl

variable {c : Cfg}

theorem SS.tEntry_arg0 (h : SS G σ c s) {L u bits : Nat} (regs : TArgs G L u bits s) :
    stackArg (tEntry G L u s) 0 = G.sp + BitVec.ofNat 32 fUsedOut := by
  have := h.gi.sp176
  show stackArg (pushed (.r4 :: [.r5, .r6, .r7, .r8, .r9, .r10, .r11]) s) 0 = _
  rw [pushed_arg0 (by rw [h.gi.sp]; show 4 * (7 + 1) ≤ G.sp.toNat; omega_arith), regs.2.2.2.2.1]

theorem SS.tEntry_arg1 (h : SS G σ c s) {L u bits : Nat} (regs : TArgs G L u bits s) :
    stackArg (tEntry G L u s) 1 = BitVec.ofNat 32 bits := by
  have := h.gi.sp176
  show stackArg (pushed (.r4 :: .r5 :: [.r6, .r7, .r8, .r9, .r10, .r11]) s) 1 = _
  rw [pushed_arg1 (by rw [h.gi.sp]; show 4 * (6 + 2) ≤ G.sp.toNat; omega_arith), regs.2.2.2.2.2]

/-- The pushed words leave `scratch`. -/
theorem SS.push_scr (h : SS G σ c s) {o n : Nat} (ho : o + n ≤ G.scrLen * 8) {k : Nat} (hk : k < n) :
    (pushed callPush s).mem (G.sa o + BitVec.ofNat 64 k) = s.mem (G.sa o + BitVec.ofNat 64 k) := by
  have := h.gi.sp176
  refine (FrameStack.pushed_frameA (rs := callPush) (s := s) (by rw [h.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith)).bytes
    (R := G.rs o n) (fun r hr => ?_) (by have := h.gi.scrFit; show n ≤ 2 ^ 64; omega_arith) hk
  simp only [List.mem_singleton] at hr; subst hr
  rw [h.gi.sp]
  exact (h.gi.scr_below ho).sub_right h.gi.pushSub

/-- The test's arguments meet its precondition. -/
theorem SS.tEntry_pin (h : SS G σ c s) {L u bits : Nat} (hL : L = G.pLen) (regs : TArgs G L u bits s)
    (hbits : bits ∈ Impl.Dsa.Arm.ProbablePrime.sizes) (hu : u ≤ G.witLen) (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) :
    PIn bits (tEntry G L u s) := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  have s176 := gi.sp176
  have spHi := gi.spHi
  have hLv := h.lens
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  obtain a1 := h.tEntry_arg1 (L := L) (u := u) regs
  obtain ⟨r0, r1, r2, r3, r4, r5⟩ := regs
  have sp : s.sp = G.sp := gi.sp
  obtain esp : (tEntry G L u s).sp = G.sp - BitVec.ofNat 32 32 := by rw [tEntry_sp, sp]; rfl
  obtain espN : (tEntry G L u s).sp.toNat = G.sp.toNat - 32 := by rw [esp, FrameStack.sub_toNat' (by omega_arith)]
  obtain a0 := h.tEntry_arg0 (L := L) ⟨r0, r1, r2, r3, r4, r5⟩
  obtain e0 : (tEntry G L u s).gpr .r0 = G.scr + BitVec.ofNat 32 sA := by rw [tEntry_gpr (by decide), r0]
  obtain e1 : (tEntry G L u s).gpr .r1 = BitVec.ofNat 32 (wa L / 8) := by rw [tEntry_gpr (by decide), r1]
  obtain e2 : (tEntry G L u s).gpr .r2 = G.randP u := by rw [tEntry_gpr (by decide), r2]
  obtain e3 : (tEntry G L u s).gpr .r3 = BitVec.ofNat 32 (G.witLen - u) := by rw [tEntry_gpr (by decide), r3]
  subst hL
  obtain wl := wa_toNat hLv
  obtain aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (by simp only [wa]; omega_arith)
  obtain aA : stackArgAddr (tEntry G G.pLen u s) 0 =
      State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)) := by
    rw [stackArgAddr, esp]; rfl
  -- The regions, as the search sees them.
  obtain scrW : Region.Sub ⟨State.addr (G.scr + BitVec.ofNat 32 sA), (BitVec.ofNat 32 (wa G.pLen / 8)).toNat * 8⟩
      G.rScr := by rw [aS, wl]; exact sw G (by simp only [sK] at big; omega_arith)
  obtain usedF : Region.Sub ⟨State.addr (G.sp + BitVec.ofNat 32 fUsedOut), 8⟩ G.rFrame := by
    rw [gi.usedAddr]; exact Offset.sub_base _ (by simp only [fUsedOut, F]; omega_arith)
  obtain argB : Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 (4 * callPush.length) + BitVec.ofNat 32 (4 * 0)), 8⟩
      G.rBelow := fun a ha => gi.pushSub a (gi.argSub a ha)
  obtain randW := gi.randSub hu
  have pre := gi.pre
  obtain fW := pre.fW; have wC := pre.wC; rw [gi.hG] at fW wC
  obtain stk : Region.Sub ⟨State.addr (tEntry G G.pLen u s).sp - 144#64, 144⟩ G.rBelow := by
    rw [esp]; exact gi.testSub
  have sv := pre.spLo
  refine ⟨hbits, a1, by omega_arith, by omega_arith, by rw [State.withRegions_rd, e2, e3, aA],
    by rw [State.withRegions_wr, e0, e1, a0],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0, e1, e2, e3]; exact (wC.symm.sub_left scrW).sub_right randW
  · rw [e0, e1, a0]; exact (gi.frame_scr.symm.sub_left scrW).sub_right usedF
  · rw [e0, e1, aA]; exact ((gi.scr_below (o := sA) (n := wa G.pLen) (by simp only [sK] at big; omega_arith)).sub_left
      (by rw [aS, wl]; exact fun _ h => h)).sub_right argB
  · rw [e2, e3, a0]; exact ((fW.symm.sub_left randW).sub_right gi.frameSub).sub_right usedF
  · rw [a0, aA]; exact (gi.frame_below.sub_left usedF).sub_right argB
  · rw [e0, e1]; exact ((gi.scr_below (o := sA) (n := wa G.pLen) (by simp only [sK] at big; omega_arith)).sub_left
      (by rw [aS, wl]; exact fun _ h => h)).symm.sub_left stk
  · rw [e2, e3]; exact ((fW.symm.sub_left randW).sub_right gi.belowSub).symm.sub_left stk
  · rw [a0]; exact (gi.frame_below.sub_left usedF).symm.sub_left stk
  · rw [aA, esp]
    have : State.addr (G.sp - BitVec.ofNat 32 32 + BitVec.ofNat 32 (4 * 0)) = State.addr (G.sp - BitVec.ofNat 32 32) := by
      rw [Nat.mul_zero, BitVec.add_zero]
    rw [show (4 * callPush.length) = 32 from rfl, this]
    exact (Offset.base_disjoint_below _ (n := 144) (k := 8) (by omega_arith)).symm
  · rw [e0, e1, wl, h.toNat (by simp only [sK]; omega_arith)]; simp only [sK] at big; omega_arith
  · rw [e2, e3, gi.randLen]; exact gi.randFit hu
  · rw [a0, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := fUsedOut) (by decide),
      Nat.mod_eq_of_lt (by simp only [fUsedOut, F] at *; omega_arith)]; simp only [fUsedOut, F] at *; omega_arith
  · rw [e1]; have := wl; omega_arith
  all_goals
    obtain hc : candOf bits (tEntry G G.pLen u s) = Spec.Dsa.decodeBE cb := by
      show Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (pushed callPush s).mem
        (State.addr ((tEntry G G.pLen u s).gpr .r0) + BitVec.ofNat 64 0) (bits / 8)) = _
      rw [e0, aS, BitVec.add_zero, ← hcb]
      refine congrArg _ (List.map_congr_left fun k hk => ?_)
      exact h.push_scr (o := sA) (n := bits / 8) (by simp only [sK] at big; omega_arith) (List.mem_range.mp hk)
    rw [hc]
  · exact hodd
  · exact hbl

/-- The regions the test is given are the caller's, the push's and the frame's. -/
theorem SS.tCovers (h : SS G σ c s) {L u : Nat} (hL : L = G.pLen) (hu : u ≤ G.witLen) :
    Covers (tRd G u ++ tWr G L) ((pushed callPush s).rd ++ (pushed callPush s).wr) ∧
      Covers (tWr G L) (pushed callPush s).wr := by
  have gi := h.gi
  have big := gi.scrBig
  have s176 := gi.sp176
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  obtain wl := wa_toNat h.lens
  obtain aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (by simp only [wa]; omega_arith)
  obtain hpw : (pushed callPush s).wr = belowA G.sp 32 :: G.rFrame :: σ.wr := by
    rw [pushed_wr, gi.wr, gi.sp]; rfl
  obtain hpr : (pushed callPush s).rd = σ.rd := by rw [pushed_rd, gi.rd]
  obtain hw : Covers (tWr G G.pLen) (pushed callPush s).wr := by
    rw [hpw]
    refine Covers.pair (Covers.one ⟨G.rScr, by rw [gi.pre.wr, gi.hG]; simp, ?_⟩)
      (Covers.one ⟨G.rFrame, by simp, ?_⟩)
    · have : sA = 4096 := rfl
      rw [aS, wl]; exact Offset.contains_base _ (by simp only [sK] at big; omega_arith) (by have := gi.scrFit; omega_arith)
    · rw [gi.usedAddr]; exact Offset.contains_base _ (by simp only [fUsedOut, F]; omega_arith) (by decide)
  refine ⟨Covers.append_left (Covers.pair ?_ ?_) hw.right, hw⟩
  · exact Covers.left (Covers.one ⟨G.rWit, by rw [hpr, gi.pre.rd, gi.hG]; simp, gi.randIn hu⟩)
  · refine Covers.right (Covers.one ⟨belowA G.sp 32, by rw [hpw]; simp, ?_⟩)
    show (_ - _ : Addr).toNat + 8 ≤ 32
    rw [show (4 * callPush.length) = 32 from rfl, Nat.mul_zero, BitVec.add_zero, BitVec.sub_self,
      BitVec.toNat_zero]; omega_arith

theorem SS.tEntry_cand (h : SS G σ c s) {L u bits b : Nat} (hL : L = G.pLen) (regs : TArgs G L u b s)
    (hb8 : bits / 8 ≤ wa L) {cb : List Byte} (hcb : Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb) :
    candOf bits (tEntry G L u s) = Spec.Dsa.decodeBE cb := by
  have big := h.gi.scrBig
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  obtain aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen) (by simp only [sK]; omega_arith)
    (by simp only [wa]; omega_arith)
  show Spec.Dsa.decodeBE (Spec.Rsa.bytesAt (pushed callPush s).mem
    (State.addr ((tEntry G G.pLen u s).gpr .r0) + BitVec.ofNat 64 0) (bits / 8)) = _
  rw [tEntry_gpr (by decide), regs.1, aS, BitVec.add_zero, ← hcb]
  refine congrArg _ (List.map_congr_left fun k hk => ?_)
  exact h.push_scr (o := sA) (n := bits / 8) (by simp only [sK] at big; omega_arith) (List.mem_range.mp hk)

theorem SS.tEntry_rand (h : SS G σ c s) {L u bits : Nat} (regs : TArgs G L u bits s) (hu : u ≤ G.witLen) :
    Spec.Rsa.bytesAt (tEntry G L u s).mem (State.addr ((tEntry G L u s).gpr .r2))
      ((tEntry G L u s).gpr .r3).toNat = G.witB.drop u := by
  have gi := h.gi
  have s176 := gi.sp176
  rw [tEntry_gpr (by decide), tEntry_gpr (by decide), regs.2.2.1, regs.2.2.2.1, gi.randLen, tEntry_mem,
    ← gi.randBytes hu]
  refine VG.Proof.Dsa.Generation.frame_bytesAt (FrameStack.pushed_frameA (rs := callPush) (s := s)
    (by rw [gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith)) (fun r hr => ?_) (by have := gi.witLt; omega_arith)
  simp only [List.mem_singleton] at hr; subst hr
  obtain fW := gi.pre.fW; rw [gi.hG] at fW
  rw [gi.sp]
  obtain rs := gi.randSub hu
  rw [GP.rRand, gi.randLen] at rs
  exact ((fW.symm.sub_left rs).sub_right gi.belowSub).sub_right gi.pushSub

/-- The test's call: its effects. -/
theorem SS.primeCall_ok (h : SS G σ c s) {L u bits : Nat} {name : String} {code : Prog isa}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (regs : TArgs G L u bits s) (hu : u ≤ G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) {cb : List Byte}
    (hcb : Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb)
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits)
    {Q : State → Prop}
    (k : ∀ t, (∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], t.gpr r = s.gpr r) → t.sp = s.sp → t.rd = s.rd →
      t.wr = s.wr → Frame [G.rs sA (wa L), G.rU, G.rBelow] s.mem t.mem →
      (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u)) →
      (∀ b rest, Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u) = some (b, rest) →
        t.mem.readW (State.addr G.sp + BitVec.ofNat 64 fUsedOut) 64 = BitVec.ofNat 64 (G.witLen - u - rest.length)) →
      Q t) :
    WP isa (callWith name code) s Q := by
  have gi := h.gi
  have s176 := gi.sp176
  obtain pin := h.tEntry_pin hL regs ok.sized hu hsize hb8 hcb hodd hbl
  obtain ⟨hc, hw⟩ := h.tCovers (u := u) hL hu
  have sp : s.sp = G.sp := gi.sp
  have big := gi.scrBig
  unfold callWith
  refine WP.frame (rs := callPush) (r := .r4) (by decide) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith) (by decide) ?_
  refine FrameStack.WP.callF ok.verified.1 (pre_of_pin pin) hc hw
    (by rw [pushed_sp, sp, FrameStack.sub_toNat' (by show 4 * 8 ≤ G.sp.toNat; omega_arith)]; have := ok.stack
        show armStack code ≤ G.sp.toNat - 4 * 8; omega_arith)
    fun s₂ hrd hwr hsp hf hg hpost => ?_
  obtain pp := ppost_of_post pin.bits hpost
  obtain ⟨r0, -, used⟩ := pp
  simp only [State.withRegions_gpr, State.withRegions_mem] at r0 used
  -- The test's result, in terms of the search.
  obtain res : resOf bits (tEntry G L u s) = Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u) := by
    unfold resOf; rw [h.tEntry_cand hL regs hb8 hcb, h.tEntry_rand regs hu]
  rw [res] at r0 used
  obtain pg : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → (popped .r4 (4 * callPush.length) s₂).gpr r = s.gpr r :=
    fun r h4 hp hl => by rw [popped_gpr h4, hg r hp hl, pushed_gpr]
  obtain mem : ∀ r ∈ [Reg.r5, .r6, .r7, .r8, .r9, .r10, .r11], r ≠ .r4 ∧ r ∈ preserved ∧ r ≠ .lr := by decide
  refine k _ (fun r hr => pg r (mem r hr).1 (mem r hr).2.1 (mem r hr).2.2)
    (by rw [popped_sp, hsp, pushed_sp, BitVec.sub_add_cancel])
    (by rw [popped_rd, hrd, pushed_rd]) (by rw [popped_wr, hwr, pushed_wr, List.tail_cons]) ?_
    (by rw [popped_gpr (by decide)]; exact r0) fun b rest e => ?_
  · have bl : Region.Sub (belowA G.sp 176) G.rBelow := by
      show Region.Sub ⟨State.addr (G.sp - BitVec.ofNat 32 176), 176⟩ ⟨State.addr G.sp - 176#64, 176⟩
      rw [FrameStack.addr_sub' (by omega_arith)]; exact fun _ h => h
    obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
    obtain aS : State.addr (G.scr + BitVec.ofNat 32 sA) = G.sa sA := h.addr (n := wa G.pLen)
      (by simp only [sK] at big ⊢; omega_arith) (by simp only [wa]; omega_arith)
    rw [popped_mem]
    refine ((FrameStack.pushed_frameA (rs := callPush) (s := s) (by rw [sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith)).sub
      fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨G.rBelow, by simp, by rw [sp]; exact gi.pushSub⟩
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · refine ⟨G.rs sA (wa L), List.mem_cons_self, ?_⟩
        rw [aS, wa_toNat (hL ▸ h.lens)]; exact fun _ h => h
      · exact ⟨G.rU, by simp, by rw [gi.usedAddr]; exact fun _ h => h⟩
      · refine ⟨G.rBelow, by simp, fun a ha => bl a ?_⟩
        rw [pushed_sp, sp] at ha
        exact FrameStack.belowA_inner (a := armStack code) (k := 4 * callPush.length) (b := 176)
          (by have := ok.stack; show armStack code + 32 ≤ 176; omega_arith) (by omega_arith) a ha
  · have := used b rest e
    rw [h.tEntry_arg0 regs, gi.usedAddr, State.callEntry_gpr _ (by decide), pushed_gpr, regs.2.2.2.1,
      gi.randLen] at this
    simp only [Spec.Rsa.wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero,
      List.cons.injEq, and_true] at this
    rw [popped_mem]; exact this

end

/-- The test's call in two runs at the same stage, with the same candidate. -/
theorem primeCall_ct {G : GP} {c : Cfg} {L u bits : Nat} {name : String} {code : Prog isa}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (hu : u ≤ G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) {cb : List Byte}
    (hodd : Spec.Dsa.decodeBE cb % 2 = 1) (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) :
    RelCT isa (fun s₁ s₂ => (∃ σ, SS G σ c s₁) ∧ TArgs G L u bits s₁ ∧
        Spec.Rsa.bytesAt s₁.mem (G.sa sA) (bits / 8) = cb ∧
        (∃ σ, SS G σ c s₂) ∧ TArgs G L u bits s₂ ∧ Spec.Rsa.bytesAt s₂.mem (G.sa sA) (bits / 8) = cb)
      (callWith name code) fun _ _ => True := by
  unfold callWith
  refine RelCT.frame (fun s₁ s₂ ⟨⟨_, h₁⟩, _, _, ⟨_, h₂⟩, _, _⟩ => by rw [h₁.gi.sp, h₂.gi.sp]) ?_
  intro a b ta tb a' b' hp ea eb
  obtain ⟨t₁, t₂, ⟨⟨σ₁, h₁⟩, g₁, c₁, ⟨σ₂, h₂⟩, g₂, c₂⟩, p₁, p₂⟩ := hp
  have s₁ := h₁.gi.sp176
  have s₂ := h₂.gi.sp176
  rw [push_pushed (by decide) (by rw [h₁.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith), Option.some.injEq] at p₁
  rw [push_pushed (by decide) (by rw [h₂.gi.sp]; show 4 * 8 ≤ G.sp.toNat; omega_arith), Option.some.injEq] at p₂
  subst p₁ p₂
  refine RelCT.call (P := fun x y => x = pushed callPush t₁ ∧ y = pushed callPush t₂) (k := primeK)
    ok.verified.1 ok.verified.2.1 (tRd G u) (tWr G L) (fun _ _ ⟨r₁, r₂⟩ => ?_) _ _ _ _ _ _ ⟨rfl, rfl⟩ ea eb
  subst r₁ r₂
  obtain ⟨cv₁, w₁⟩ := h₁.tCovers (u := u) hL hu
  obtain ⟨cv₂, w₂⟩ := h₂.tCovers (u := u) hL hu
  obtain pin₁ := h₁.tEntry_pin hL g₁ ok.sized hu hsize hb8 c₁ hodd hbl
  refine ⟨pre_of_pin pin₁, pre_of_pin (h₂.tEntry_pin hL g₂ ok.sized hu hsize hb8 c₂ hodd hbl),
    pub_of ?_ ?_ ?_ ?_ ?_ ?_ ?_ pin₁.bits ?_ ?_, cv₁, w₁, cv₂, w₂⟩
  · show (pushed callPush t₁).sp = (pushed callPush t₂).sp
    rw [pushed_sp, pushed_sp, h₁.gi.sp, h₂.gi.sp]
  · show (tEntry G L u t₁).gpr .r0 = (tEntry G L u t₂).gpr .r0
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.1, g₂.1]
  · show (tEntry G L u t₁).gpr .r1 = (tEntry G L u t₂).gpr .r1
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.2.1, g₂.2.1]
  · show (tEntry G L u t₁).gpr .r2 = (tEntry G L u t₂).gpr .r2
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.2.2.1, g₂.2.2.1]
  · show (tEntry G L u t₁).gpr .r3 = (tEntry G L u t₂).gpr .r3
    rw [tEntry_gpr (by decide), tEntry_gpr (by decide), g₁.2.2.2.1, g₂.2.2.2.1]
  · rw [h₁.tEntry_arg0 g₁, h₂.tEntry_arg0 g₂]
  · rw [h₁.tEntry_arg1 g₁, h₂.tEntry_arg1 g₂]
  · rw [h₁.tEntry_cand hL g₁ hb8 c₁, h₂.tEntry_cand hL g₂ hb8 c₂]
  · rw [h₁.tEntry_rand g₁ hu, h₂.tEntry_rand g₂ hu]

end VG.Proof.Dsa.Arm.Gen

end

end


/-! # DSA parameter generation on ARMv7: a probable-prime test (`test_vp`)

`test L name code` tests the candidate at `sA` with the witnesses from
`fUsed` on: `fRes` := its status, and `fUsed` := the witnesses it read when
the tape sufficed (`testCfg`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Gen
open VG VG.Arm VG.Proof.Rsa.Arm.Keys
open VG.Impl.Dsa.Arm.Generation
open VG.Impl.Dsa.Arm.ProbablePrime (keyOff keyWords layout)
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_movw wp_dp wp_subs wp_cmp op2_reg op2_imm dpVal eval_eq
  ofNat_beq_zero)
open VG.Proof.Rsa.Arm.Recover (VP)

/-- The stage after a test, from its result `res`. -/
def testCfg (c : Cfg) (cl : Claims) (witLen : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }.setV fRes 0
  | some (b, rest) => ({ c with cl := cl }.setV fRes (BitVec.ofNat 32 (if b then 1 else 2))).setV fUsed
      (BitVec.ofNat 32 (witLen - rest.length))

section
variable {G : GP}

/-- A stage: a state of the search with the contents `c`, and `X` of the run. -/
abbrev St (G : GP) (c : Cfg) (X : State → Prop) (σ s : State) : Prop := SS G σ c s ∧ X σ

theorem varOk_of {o : Nat}
    (h : 40 ≤ o ∧ o + 4 ≤ F ∧ o % 4 = 0 ∧ o ∉ [fOut, fUsedP, fStP, fScratch, fWit, fWitLen]) : VarOk G o := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun p hp e => h.2.2.2 ?_⟩
  simp only [fixedWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [e]

theorem varOk_fRes : VarOk G fRes := varOk_of (by decide)
theorem varOk_fUsed : VarOk G fUsed := varOk_of (by decide)
theorem varOk_fUsedOut : VarOk G fUsedOut := varOk_of (by decide)

/-- A fixed frame word's value. -/
theorem SS.fixedV {σ s : State} {c : Cfg} (h : SS G σ c s) {o : Nat} {v : BitVec 32} (hp : (o, v) ∈ fixedWords G) :
    fw s.mem G o = v := h.gi.fixed (o, v) hp

theorem SS.slotV {σ s : State} {c : Cfg} (h : SS G σ c s) {o : Nat} (ho : o ∈ c.LS) : fw s.mem G o = c.V o :=
  h.gi.slots o ho

/-! ## The arguments -/

variable {c : Cfg} {X : State → Prop}

/-- `r0` and `r1`: the working space; `r5`: the size. -/
abbrev TR1 (G : GP) (L bits : Nat) (s : State) : Prop :=
  s.gpr .r0 = G.scr + BitVec.ofNat 32 sA ∧ s.gpr .r1 = BitVec.ofNat 32 (wa L / 8) ∧ s.gpr .r5 = BitVec.ofNat 32 bits

theorem targs1_vp {L bits : Nat} (hL : L = G.pLen) (hb : bits < 2 ^ 16) :
    VP (St G c X) (.block (scr L .r0 sA ++
        ([.movw .r1 (BitVec.ofNat 16 (wa L / 8)), .movw .r5 (BitVec.ofNat 16 bits)] : List Instr)))
      (fun σ s => St G c X σ s ∧ TR1 G L bits s) := by
  refine VP.taint [.r8] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r8])
      (.block (scr 128 .r0 sA ++ [.movw .r1 (BitVec.ofNat 16 5), .movw .r5 (BitVec.ofNat 16 5)])), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.1.r8, h₂.1.r8])
    fun σ s ⟨h, x⟩ => ?_
  have big := h.gi.scrBig
  have hLv := h.lens
  subst hL
  refine scr_ok (d := .r0) h.r8 rfl hLv (by simp only [sK]; omega_arith) fun s₁ v₁ R₁ M₁ => wp_movw fun t₁ u₁ =>
    wp_movw fun t u => WP.block_nil ⟨⟨((h.of_rest R₁ M₁).of_rest (u₁.rest (ws := [.r1]) (by simp)) u₁.mem).of_rest
      (u.rest (ws := [.r5]) (by simp)) u.mem, x⟩, by rw [u.other _ (by decide), u₁.other _ (by decide)]; exact v₁, ?_, ?_⟩
  · rw [u.other _ (by decide), u₁.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, wa]; rcases hLv with e | e | e <;> rw [e]
  · rw [u.gpr]; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega_arith)]

/-- A load of a frame word whose value is known, keeping a stage. -/
theorem SS.ldK {σ s : State} (h : SS G σ c s) {o : Nat} (ho : o + 4 ≤ F + 16) (h4 : o % 4 = 0) {v : BitVec 32}
    (hv : fw s.mem G o = v) {t : Reg} (h7 : t ≠ .r7) (h8 : t ≠ .r8) (h9 : t ≠ .r9) {rest : List Instr}
    {Q : State → Prop} (k : ∀ s', SS G σ c s' → Upd s s' t v → WP isa (.block rest) s' Q) :
    WP isa (.block (.ldrSp t o :: rest)) s Q :=
  h.gi.ldV ho h4 hv fun s' u => k s' (h.of_rest (u.rest (ws := [t]) (by simp)) u.mem (by simpa using h7.symm)
    (by simpa using h8.symm) (by simpa using h9.symm)) u

theorem targs2_vp {L u bits : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u) :
    VP (fun σ s => St G c X σ s ∧ TR1 G L bits s) (.block [ld .r4 fUsed, ld .r2 fWit, ld .r3 fWitLen])
      (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r4 = BitVec.ofNat 32 u ∧ s.gpr .r2 = G.wit ∧
        s.gpr .r3 = BitVec.ofNat 32 G.witLen) := by
  refine VP.ldrSp (c := [(.r4, fUsed), (.r2, fWit), (.r3, fWitLen)])
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.1.1.gi.sp, h₂.1.1.gi.sp]) fun σ s ⟨⟨h, x⟩, r0, r1, r5⟩ => ?_
  refine h.ldK (o := fUsed) (by decide) (by decide) ((h.slotV hU).trans hUv) (by decide) (by decide) (by decide)
    fun s₁ h₁ u₁ => ?_
  refine h₁.ldK (o := fWit) (by decide) (by decide) (h₁.fixedV (v := G.wit) (by simp [fixedWords])) (by decide) (by decide)
    (by decide) fun s₂ h₂ u₂ => ?_
  refine h₂.ldK (o := fWitLen) (by decide) (by decide) (h₂.fixedV (v := BitVec.ofNat 32 G.witLen) (by simp [fixedWords])) (by decide) (by decide)
    (by decide) fun s₃ h₃ u₃ => WP.block_nil ⟨⟨h₃, x⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, u₃.gpr⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r0]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r1]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), r5]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₃.other _ (by decide), u₂.gpr]

theorem targs3_vp {L u bits : Nat} (hu : u ≤ G.witLen) :
    VP (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r4 = BitVec.ofNat 32 u ∧ s.gpr .r2 = G.wit ∧
        s.gpr .r3 = BitVec.ofNat 32 G.witLen)
      (.block [.dp .add .r2 .r2 (.reg .r4), .dp .sub .r3 .r3 (.reg .r4), .addSp .r4 fUsedOut, .cmp .r3 (.imm 0)])
      (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r2 = G.wit + BitVec.ofNat 32 u ∧
        s.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) ∧ s.gpr .r4 = G.sp + BitVec.ofNat 32 fUsedOut ∧
        s.z = decide (u = G.witLen)) := by
  refine VP.taint [.r2, .r3, .r4] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r2, .r3, .r4])
      (.block [.dp .add .r2 .r2 (.reg .r4), .dp .sub .r3 .r3 (.reg .r4), .addSp .r4 fUsedOut, .cmp .r3 (.imm 0)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ ⟨_, _, a₁, b₁, c₁⟩ ⟨_, _, a₂, b₂, c₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [b₁, b₂]
      · rw [c₁, c₂]
      · rw [a₁, a₂]) fun σ s ⟨⟨h, x⟩, ⟨r0, r1, r5⟩, r4, r2, r3⟩ => ?_
  have wl := h.gi.witLt
  refine wp_dp (op2_reg _ _) fun s₁ u₁ => wp_dp (op2_reg _ _) fun s₂ u₂ =>
    VG.Proof.Bignum.Arm.wp_stackAddr (by decide) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil ?_
  obtain R : Rest [.r2, .r3, .r4] s t := (((u₁.rest (by simp)).trans (u₂.rest (by simp))).trans (u₃.rest (by simp))).trans
    (f.rest _)
  obtain v3 : s₂.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) := by
    rw [u₂.gpr, dpVal, u₁.other _ (by decide), u₁.other _ (by decide), r3, r4,
      BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith)]
  obtain t3 : t.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) := by rw [f.gpr, u₃.other _ (by decide), v3]
  refine ⟨⟨h.of_rest R (by rw [f.mem, u₃.mem, u₂.mem, u₁.mem]), x⟩, ⟨?_, ?_, ?_⟩, ?_, t3, ?_, ?_⟩
  · rw [R.gpr _ (by decide), r0]
  · rw [R.gpr _ (by decide), r1]
  · rw [R.gpr _ (by decide), r5]
  · rw [f.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, dpVal, r2, r4]
  · rw [f.gpr, u₃.gpr, u₂.sp, u₁.sp, h.gi.sp]
  · have e0 : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
    rw [z, u₃.other _ (by decide), v3, e0, ofNat_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]; omega_arith

theorem targs4_vp {L u bits : Nat} :
    VP (fun σ s => St G c X σ s ∧ TR1 G L bits s ∧ s.gpr .r2 = G.wit + BitVec.ofNat 32 u ∧
        s.gpr .r3 = BitVec.ofNat 32 (G.witLen - u) ∧ s.gpr .r4 = G.sp + BitVec.ofNat 32 fUsedOut ∧
        s.z = decide (u = G.witLen))
      (.ite .eq (.block [ld .r2 fWit]) (.block [])) (fun σ s => St G c X σ s ∧ TArgs G L u bits s) := by
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [eval_eq, eval_eq, h₁.2.2.2.2.2, h₂.2.2.2.2.2]) ?_ ?_
  · refine VP.ld (SS.spOk (c := fun _ => c) fun σ s h => h.1.1.1) fun σ s ⟨⟨⟨h, x⟩, ⟨r0, r1, r5⟩, r2, r3, r4, z⟩, e⟩ => ?_
    obtain hu : u = G.witLen := by rw [eval_eq, z] at e; simpa using e
    refine h.ldK (o := fWit) (by decide) (by decide) (h.fixedV (v := G.wit) (by simp [fixedWords])) (by decide)
      (by decide) (by decide) fun t ht ut => WP.block_nil ⟨⟨ht, x⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ut.other _ (by decide), r0]
    · rw [ut.other _ (by decide), r1]
    · rw [ut.gpr, GP.randP, ite_eq_left hu]
    · rw [ut.other _ (by decide), r3]
    · rw [ut.other _ (by decide), r4]
    · rw [ut.other _ (by decide), r5]
  · refine VP.block_nil fun σ s ⟨⟨hx, ⟨r0, r1, r5⟩, r2, r3, r4, z⟩, e⟩ => ⟨hx, r0, r1, ?_, r3, r4, r5⟩
    obtain hu : u ≠ G.witLen := by rw [eval_eq, z] at e; simpa using e
    rw [r2, GP.randP, ite_eq_right hu]

/-! ## The call -/

/-- One more known frame word. -/
theorem GI.addSlot {σ t : State} {V : Nat → BitVec 32} {LS : List Nat} (h : GI G σ V LS t) {o : Nat} (ho : VarOk G o)
    {v : BitVec 32} (hv : fw t.mem G o = v) : GI G σ (upd V o v) (o :: LS) t := by
  refine ⟨h.pre, h.hG, h.sp, h.rd, h.wr, h.saved, h.fixed, fun o' ho' => ?_, fun o' ho' => ?_, h.frame⟩
  · by_cases e : o' = o
    · subst e; rw [upd_self]; exact hv
    · rw [upd_ne _ _ e]; exact h.slots o' (List.mem_of_ne_of_mem e ho')
  · rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ho
    · exact h.ls o' ho'

/-- Through the test's call: claims apart from its working space kept. -/
theorem SS.of_call {σ s t : State} {L : Nat} (h : SS G σ c s) (hL : L = G.pLen)
    (g : ∀ r ∈ [Reg.r7, .r8, .r9], t.gpr r = s.gpr r) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (f : Frame [G.rs sA (wa L), G.rU, G.rBelow] s.mem t.mem) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    {cl' : Claims} (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa L) x) : SS G σ { c with cl := cl' } t := by
  have gi := h.gi
  have big := gi.scrBig
  have fit := gi.scrFit
  obtain kz0 : 0 < kz G.pLen := by simp only [kz]; omega_arith
  subst hL
  have sA4 : sA + wa G.pLen = sK G.pLen := rfl
  obtain R : Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r10, .r11, .r12, .lr] s t :=
    ⟨fun r hr => g r (by cases r <;> simp_all), rd, wr, sp⟩
  obtain fs : Frame [G.rScr, G.rU, G.rBelow] s.mem t.mem := f.sub fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨G.rScr, List.mem_cons_self, sw G (by omega_arith)⟩
    · exact ⟨G.rU, by simp, fun _ h => h⟩
    · exact ⟨G.rBelow, by simp, fun _ h => h⟩
  obtain uF : Region.Sub G.rU G.rFrame := Offset.sub_base _ (by simp only [fUsedOut, F]; omega_arith)
  obtain kd : ∀ r' ∈ [G.rs sA (wa G.pLen), G.rU, G.rBelow], G.rK.Disjoint r' := fun r' hr' => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    show Region.Disjoint ⟨State.addr G.KB, _⟩ _
    rw [gi.kaddr]
    rcases hr' with rfl | rfl | rfl
    · exact gi.sdisj (.inr (by omega_arith)) big (by omega_arith)
    · exact (gi.scr_frame big).sub_right uF
    · exact gi.scr_below big
  refine ⟨gi.of_used R fs h88 h92, (g _ (by simp)).trans h.r7, (g _ (by simp)).trans h.r8, (g _ (by simp)).trans h.r9,
    fun x hx => ?_, fun x hx => h.clOk x (hcl x hx).1, fun j hj => ?_, h.liveOk, fun d hd => ?_, h.kslOk⟩
  · obtain ⟨hm, ha⟩ := hcl x hx
    have := h.clOk x hm
    rw [VG.Proof.Dsa.Generation.frame_bytesAt f (fun r' hr' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact gi.sdisj ha (by omega_arith) (by omega_arith)
      · exact (gi.scr_frame (by omega_arith)).sub_right uF
      · exact gi.scr_below (by omega_arith)) (by omega_arith)]
    exact h.sb x hm
  · rw [num_frame h.lens f kd (h.liveOk j hj)]; exact h.arrs j hj
  · rw [slot_frame h.lens f kd (h.kslOk d hd)]; exact h.ksl d hd

/-- After the call: the count's word known when the tape sufficed. -/
def callCfg (c : Cfg) (cl : Claims) (witLen u : Nat) : Option (Bool × Spec.RsaKeyGen.Rand) → Cfg
  | none => { c with cl := cl }
  | some (_, rest) => { c with cl := cl }.setV fUsedOut (BitVec.ofNat 32 (witLen - u - rest.length))

theorem primeCall_vp {L u bits : Nat} {name : String} {code : Prog isa} {cb : List Byte} {cl' : Claims}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (hu : u ≤ G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) (hcb : (sA, cb) ∈ c.cl)
    (hcbl : cb.length = bits / 8) (hodd : Spec.Dsa.decodeBE cb % 2 = 1)
    (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa L) x) :
    VP (fun σ s => St G c X σ s ∧ TArgs G L u bits s) (callWith name code)
      (fun σ t => St G (callCfg c cl' G.witLen u (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u))) X σ t ∧
        (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status
          (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u))) := by
  obtain bytes : ∀ σ s, SS G σ c s → Spec.Rsa.bytesAt s.mem (G.sa sA) (bits / 8) = cb := fun σ s h => by
    have := h.sb _ hcb; rwa [hcbl] at this
  refine VP.of_ct (fun σ₁ σ₂ => (primeCall_ct (c := c) ok hL hu hsize hb8 hodd hbl).mono
    (fun s₁ s₂ ⟨⟨⟨h₁, _⟩, g₁⟩, ⟨⟨h₂, _⟩, g₂⟩⟩ => ⟨⟨σ₁, h₁⟩, g₁, bytes _ _ h₁, ⟨σ₂, h₂⟩, g₂, bytes _ _ h₂⟩)
    fun _ _ _ => trivial) fun σ s ⟨⟨h, x⟩, regs⟩ => ?_
  refine h.primeCall_ok (name := name) ok hL regs hu hsize hb8 (bytes _ _ h) hodd hbl
    fun t g sp rd wr f r0 used => ⟨⟨?_, x⟩, r0⟩
  obtain h' := h.of_call hL (fun r hr => g r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp))
    sp rd wr f h88 h92 hcl
  unfold callCfg
  split
  · exact h'
  · rename_i b rest e
    refine ⟨h'.gi.addSlot varOk_fUsedOut ?_, h'.r7, h'.r8, h'.r9, h'.sb, h'.clOk, h'.arrs, h'.liveOk, h'.ksl, h'.kslOk⟩
    have := used b rest e
    show t.mem.readW _ 32 = _
    rw [Mem.readW_lo32 this]
    apply BitVec.eq_of_toNat_eq; simp

theorem status_lt (res : Option (Bool × Spec.RsaKeyGen.Rand)) : Proof.Dsa.ProbablePrime.status res < 3 := by
  unfold Proof.Dsa.ProbablePrime.status; split <;> decide

/-- The test's result into `fRes`, then Z iff the tape ran out. -/
theorem testRes_vp {c' : Cfg} {res : Option (Bool × Spec.RsaKeyGen.Rand)} :
    VP (fun σ t => St G c' X σ t ∧ (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status res)
      (.seq (.block (st .r0 fRes)) (.block [.cmp .r0 (.imm 0)]))
      (fun σ t => St G (c'.setV fRes (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res))) X σ t ∧
        isa.eval .eq t = some (decide (res = none))) := by
  obtain e0 : ∀ t : State, (t.gpr .r0).toNat = Proof.Dsa.ProbablePrime.status res →
      t.gpr .r0 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res) := fun t h =>
    BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := status_lt res; omega_arith)])
  refine VP.seq (G := fun σ t => St G (c'.setV fRes (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res))) X σ t ∧
      t.gpr .r0 = BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status res))
    (st_vp (c := fun _ => c') (fun σ t h => h.1.1) (by decide) varOk_fRes fun σ s t ⟨⟨_, x⟩, r0⟩ h R => ?_) ?_
  · rw [e0 s r0] at h
    exact ⟨⟨h, x⟩, by rw [R.gpr _ (by decide), e0 s r0]⟩
  refine VP.taint [.r0] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r0]) (.block [.cmp .r0 (.imm 0)]), rfl⟩
    (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2])
    fun σ s ⟨⟨h, x⟩, r0⟩ => wp_cmp (op2_imm (by decide)) fun t f z => WP.block_nil
      ⟨⟨h.of_rest (f.rest []) f.mem, x⟩, ?_⟩
  obtain e00 : ∀ x : BitVec 32, x - 0 = x := fun x => by simp
  rw [eval_eq, z, r0, e00, ofNat_beq_zero (by have := status_lt res; omega_arith)]
  congr 1
  unfold Proof.Dsa.ProbablePrime.status
  split <;> simp

/-- A piece no state reaches. -/
theorem VP.of_false {F Q : State → State → Prop} {c : Prog isa} (h : ∀ σ s, ¬ F σ s) : VP F c Q :=
  ⟨fun σ s hs => absurd hs (h σ s), fun _ _ _ _ _ _ ⟨σ, _, h₁, _⟩ => absurd h₁ (h σ _)⟩

/-- The witnesses a test leaves are a suffix of those it is given. -/
theorem rest_le {w : Nat} {r rest : Spec.RsaKeyGen.Rand} {b : Bool} (h : Spec.Dsa.probablePrime w r = some (b, rest)) :
    rest.length ≤ r.length :=
  (VG.Proof.Dsa.Generation.probablePrime_suffix h).length_le

/-- `fUsed` := the witnesses read, unless the tape ran out. -/
theorem testTail_vp {cl' : Claims} {u cand : Nat} (hU : fUsed ∈ c.LS) (hUv : c.V fUsed = BitVec.ofNat 32 u)
    (h88 : fUsedOut ∉ c.LS) (hwl : G.witB.length = G.witLen) (hu : u ≤ G.witLen) :
    VP (fun σ t => St G ((callCfg c cl' G.witLen u (Spec.Dsa.probablePrime cand (G.witB.drop u))).setV fRes
        (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status (Spec.Dsa.probablePrime cand (G.witB.drop u))))) X σ t ∧
        isa.eval .eq t = some (decide (Spec.Dsa.probablePrime cand (G.witB.drop u) = none)))
      (.ite .eq (.block []) (VG.Impl.Rsa.Arm.Keys.seqs [.block [ld .r1 fUsedOut, ld .r2 fUsed],
        .block [.dp .add .r2 .r2 (.reg .r1)], .block (st .r2 fUsed)]))
      (St G (testCfg c cl' G.witLen (Spec.Dsa.probablePrime cand (G.witB.drop u))) X) := by
  generalize hres : Spec.Dsa.probablePrime cand (G.witB.drop u) = res
  refine VP.ite (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by rw [h₁.2, h₂.2]) ?_ ?_
  · refine VP.block_nil fun σ s ⟨⟨⟨h, x⟩, e⟩, z⟩ => ?_
    rw [e] at z
    have : res = none := by simpa using z
    subst this
    exact ⟨h, x⟩
  rcases res with _ | ⟨b, rest⟩
  · exact VP.of_false fun σ s ⟨⟨_, e⟩, z⟩ => by rw [e] at z; simp at z
  -- The tape sufficed: `fUsed` := `u` and the count.
  obtain rl := rest_le hres
  rw [List.length_drop, hwl] at rl
  let x : BitVec 32 := BitVec.ofNat 32 (G.witLen - u - rest.length)
  let st0 : BitVec 32 := BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status (some (b, rest)))
  let c6 : Cfg := ({ c with cl := cl' }.setV fUsedOut x).setV fRes st0
  obtain v88 : c6.V fUsedOut = x := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsedOut = x; rw [upd_ne _ _ (by decide), upd_self]
  obtain vU : c6.V fUsed = BitVec.ofNat 32 u := by
    show upd (upd c.V fUsedOut x) fRes st0 fUsed = _; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide), hUv]
  refine VP.seq (G := fun σ t => St G c6 X σ t ∧ t.gpr .r1 = x ∧ t.gpr .r2 = BitVec.ofNat 32 u)
    (VP.ldrSp (c := [(.r1, fUsedOut), (.r2, fUsed)]) (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => by
      rw [h₁.1.1.1.gi.sp, h₂.1.1.1.gi.sp]) fun σ s ⟨⟨⟨h, xx⟩, _⟩, _⟩ => ?_) ?_
  · change SS G σ c6 s at h
    refine h.ldK (o := fUsedOut) (by decide) (by decide) ((h.slotV (by simp [c6])).trans v88) (by decide)
      (by decide) (by decide) fun s₁ h₁ u₁ => ?_
    refine h₁.ldK (o := fUsed) (by decide) (by decide) ((h₁.slotV (by simp [c6, hU])).trans vU) (by decide)
      (by decide) (by decide) fun s₂ h₂ u₂ => WP.block_nil ⟨⟨h₂, xx⟩, by rw [u₂.other _ (by decide), u₁.gpr], u₂.gpr⟩
  refine VP.seq (G := fun σ t => St G c6 X σ t ∧ t.gpr .r2 = BitVec.ofNat 32 (G.witLen - rest.length))
    (VP.taint [.r1, .r2] ⟨VG.Taint.hintOfSize VG.Arm.taint 256 (Taint.ofRegs [.r1, .r2])
      (.block [.dp .add .r2 .r2 (.reg .r1)]), rfl⟩
      (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h₁.2.1, h₂.2.1]
        · rw [h₁.2.2, h₂.2.2])
      fun σ s ⟨⟨h, xx⟩, r1, r2⟩ => wp_dp (op2_reg _ _) fun t ut => WP.block_nil
        ⟨⟨h.of_rest (ut.rest (ws := [.r2]) (by simp)) ut.mem, xx⟩, ?_⟩) ?_
  · rw [ut.gpr, dpVal, r2, r1]
    show BitVec.ofNat 32 u + BitVec.ofNat 32 (G.witLen - u - rest.length) = _
    rw [← BitVec.ofNat_add, show u + (G.witLen - u - rest.length) = G.witLen - rest.length by
      omega_using [rl, hu]]
  refine st_vp (c := fun _ => c6) (fun σ t h => h.1.1) (by decide) varOk_fUsed fun σ s t ⟨⟨_, xx⟩, r2⟩ h _ => ?_
  rw [r2] at h
  refine ⟨h.mono (fun o ho => ?_) (fun x hx => hx) (fun j hj => ⟨hj, rfl⟩) (fun d hd => ⟨hd, rfl⟩), xx⟩
  simp only [testCfg, c6, Cfg.setV, List.mem_cons] at ho ⊢
  rcases ho with rfl | rfl | ho
  · exact ⟨by simp, by simp [upd]⟩
  · refine ⟨by simp, ?_⟩
    simp only [upd, show fRes ≠ fUsed by decide, ite_false, ite_true]
    cases b <;> rfl
  · refine ⟨by simp [ho], ?_⟩
    obtain n88 : o ≠ fUsedOut := fun e => h88 (e ▸ ho)
    obtain e : st0 = BitVec.ofNat 32 (if b then 1 else 2) := by cases b <;> rfl
    simp only [upd, n88, ite_false, e]

theorem sized_lt {bits : Nat} (h : bits ∈ Impl.Dsa.Arm.ProbablePrime.sizes) : bits < 2 ^ 16 := by
  simp only [Impl.Dsa.Arm.ProbablePrime.sizes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The test of the candidate in `sA`, with the tape from `fUsed`, recording its
result in `fRes` and the witnesses it read in `fUsed`. -/
theorem test_vp {L u bits : Nat} {name : String} {code : Prog isa} {cb : List Byte} {cl' : Claims}
    (ok : PrimeOk bits code) (hL : L = G.pLen) (hu : u ≤ G.witLen) (hU : fUsed ∈ c.LS)
    (hUv : c.V fUsed = BitVec.ofNat 32 u) (hwl : G.witB.length = G.witLen)
    (hsize : keyOff + 8 * keyWords bits ≤ wa L) (hb8 : bits / 8 ≤ wa L) (hcb : (sA, cb) ∈ c.cl)
    (hcbl : cb.length = bits / 8) (hodd : Spec.Dsa.decodeBE cb % 2 = 1)
    (hbl : Spec.Dsa.bitLength (Spec.Dsa.decodeBE cb) = bits) (h88 : fUsedOut ∉ c.LS) (h92 : fUsedOut + 4 ∉ c.LS)
    (hcl : ∀ x ∈ cl', x ∈ c.cl ∧ Apart sA (wa L) x) :
    VP (St G c X) (test L bits name code)
      (St G (testCfg c cl' G.witLen (Spec.Dsa.probablePrime (Spec.Dsa.decodeBE cb) (G.witB.drop u))) X) :=
  VP.seq (targs1_vp hL (sized_lt ok.sized)) (VP.seq (targs2_vp hU hUv) (VP.seq (targs3_vp hu) (VP.seq targs4_vp
    (VP.seq (primeCall_vp ok hL hu hsize hb8 hcb hcbl hodd hbl h88 h92 hcl)
      (VP.assoc (VP.seq testRes_vp (testTail_vp hU hUv h88 hwl hu)))))))

end

end VG.Proof.Dsa.Arm.Gen
