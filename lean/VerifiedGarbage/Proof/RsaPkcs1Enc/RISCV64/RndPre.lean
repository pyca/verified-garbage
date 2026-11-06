module

public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.RsaPkcs1Enc.Random
public import VerifiedGarbage.Proof.RsaPkcs1Enc.RISCV64.EncCorrect
public import VerifiedGarbage.Impl.RsaPkcs1Enc.RISCV64.Random
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# RSAES-PKCS1-v1_5 encryption from a random tape on RISC-V: the precondition

`RPre s`: the shared contract's precondition (`encryptRandomContract`, with
`rndStack` bytes of stack: our frame, the call's 48 bytes of stack
arguments and the frame of `vg_rsa_pkcs1_encrypt_precomputed`), by name
(`rPre_of`), and the regions it names. The frame is
`vg_rsa_pkcs1_verify_precomputed`'s (`kR`); below it, the call's stack
arguments (`cR`) and the callee's frame, all in `lowR`.
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.RISCV64.Rnd

open VG VG.RISCV64 VG.Impl.RsaPkcs1Sig.RISCV64 VG.Proof.RsaPkcs1Sig.RISCV64

/-- The stack the function uses: our frame, the call's stack arguments and
the callee's frame. -/
def rndStack : Nat := 4304

theorem stackArgs_seven (s : State) :
    (List.range 7).map (stackArg s) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6] := rfl

/-! ## The regions -/

abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev tR (s : State) : Region := ⟨s.gpr .a2, 16⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
abbrev mR (s : State) : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
abbrev rR (s : State) : Region := ⟨stackArg s 1, (stackArg s 2).toNat⟩
abbrev scR (s : State) : Region := ⟨stackArg s 3, (stackArg s 4).toNat * 8⟩
abbrev pR (s : State) : Region := ⟨stackArg s 5, (stackArg s 6).toNat * 8⟩
abbrev a7R (s : State) : Region := ⟨stackArgAddr s 0, 56⟩
abbrev stR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 4304, 4304⟩

/-- What the code needs of `encryptRandomContract.pre`, by name. -/
structure RPre (s : State) : Prop where
  spal : s.sp.toNat % 16 = 0
  sp1 : 4304 ≤ s.sp.toNat
  sp2 : s.sp.toNat + 56 ≤ 2 ^ 64
  hrd : s.rd = [nR s, eR s, mR s, rR s, pR s, a7R s]
  hwr : s.wr = [oR s, tR s, scR s]
  ot : (oR s).Disjoint (tR s)
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  om : (oR s).Disjoint (mR s)
  orr : (oR s).Disjoint (rR s)
  os : (oR s).Disjoint (scR s)
  op : (oR s).Disjoint (pR s)
  oa : (oR s).Disjoint (a7R s)
  tn : (tR s).Disjoint (nR s)
  te : (tR s).Disjoint (eR s)
  tm : (tR s).Disjoint (mR s)
  tr : (tR s).Disjoint (rR s)
  ts : (tR s).Disjoint (scR s)
  tp : (tR s).Disjoint (pR s)
  ta : (tR s).Disjoint (a7R s)
  ns : (nR s).Disjoint (scR s)
  es : (eR s).Disjoint (scR s)
  ms : (mR s).Disjoint (scR s)
  rs : (rR s).Disjoint (scR s)
  sp : (scR s).Disjoint (pR s)
  sa : (scR s).Disjoint (a7R s)
  ko : (stR s).Disjoint (oR s)
  kt : (stR s).Disjoint (tR s)
  kn : (stR s).Disjoint (nR s)
  ke : (stR s).Disjoint (eR s)
  km : (stR s).Disjoint (mR s)
  kr : (stR s).Disjoint (rR s)
  ks : (stR s).Disjoint (scR s)
  kp : (stR s).Disjoint (pR s)
  ka : (stR s).Disjoint (a7R s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wt : (s.gpr .a2).toNat + 16 ≤ 2 ^ 64
  wn : (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64
  we : (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64
  wm : (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64
  wr : (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 64
  ws : (stackArg s 3).toNat + (stackArg s 4).toNat * 8 ≤ 2 ^ 64
  wp : (stackArg s 5).toNat + (stackArg s 6).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a4).toNat
  k2 : (s.gpr .a4).toNat ≤ 1024
  ok : (s.gpr .a1).toNat = (s.gpr .a4).toNat
  e1 : 1 ≤ (s.gpr .a6).toNat
  e2 : (s.gpr .a6).toNat ≤ (s.gpr .a4).toNat
  ml : (stackArg s 0).toNat + 11 ≤ (s.gpr .a4).toNat
  rl : (stackArg s 2).toNat ≤
    Spec.RsaPkcs1Enc.padEntropy ((s.gpr .a4).toNat - (stackArg s 0).toNat - 3)
  hs : Spec.Rsa.publicScratchWords (s.gpr .a4).toNat ≤ (stackArg s 4).toNat
  hp : (stackArg s 6).toNat = Spec.Rsa.precomputedWords (s.gpr .a4).toNat
  alt : (s.gpr .a2).toNat % 8 = 0
  als : (stackArg s 3).toNat % 8 = 0
  alp : (stackArg s 5).toNat % 8 = 0

theorem rPre_of {s : State} (h : (Spec.RsaPkcs1Enc.encryptRandomContract abi rndStack).pre s) : RPre s := by
  have e : rndStack = 4303 + 1 := rfl
  rw [e] at h
  sig_pre [Spec.RsaPkcs1Enc.encryptRandomContract, Spec.RsaPkcs1Enc.encryptRandomSig, abi, argRegs,
    stackArgs_seven, List.append_eq, List.range, List.range.loop] at h
  obtain ⟨spal, sp1, sp2, hrd, hwr, ot, on, oe, om, orr, os, op, oa, tn, te, tm, tr, ts, tp, ta, ns, es, ms, rs,
    sp, sa, ko, kt, kn, ke, km, kr, ks, kp, ka, wo, wt, wn, we, wm, wr, ws, wp, ⟨k1, k2⟩, ok, e1, e2, ml, rl, hs,
    hp, alt, als, alp⟩ := h
  exact ⟨spal, sp1, sp2, hrd, hwr, ot, on, oe, om, orr, os, op, oa, tn, te, tm, tr, ts, tp, ta, ns, es, ms, rs,
    sp, sa, ko, kt, kn, ke, km, kr, ks, kp, ka, wo, wt, wn, we, wm, wr, ws, wp, k1, k2, ok, e1, e2, ml, rl, hs,
    hp, alt, als, alp⟩

/-! ## The values -/

/-- The length of `PS`. -/
abbrev psLen (s : State) : Nat := (s.gpr .a4).toNat - (stackArg s 0).toNat - 3

abbrev nB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat
abbrev eB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat
abbrev randB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 1) (stackArg s 2).toNat
abbrev preW (s : State) : List (BitVec 64) := Spec.Rsa.wordsAt s.mem (stackArg s 5) (stackArg s 6).toNat

/-- The kept octets after `i` octets of the tape. -/
abbrev kept (s : State) (i : Nat) : List Byte := VG.Proof.RsaPkcs1Enc.nz ((randB s).take i)

/-- `PS`, in the frame. -/
abbrev psA (s : State) : Addr := fb s + BitVec.ofNat 64 oEM1

/-- The call's stack arguments, below our frame, and all of the stack below it. -/
abbrev cR (s : State) : Region := ⟨fb s - BitVec.ofNat 64 48, 48⟩
abbrev lowR (s : State) : Region := ⟨s.sp - BitVec.ofNat 64 4304, 2176⟩

section
variable {s : State}

theorem psLen_le (hp : RPre s) : psLen s ≤ 1021 := by have := hp.ml; have := hp.k2; unfold psLen; omega

theorem rl_le (hp : RPre s) : (stackArg s 2).toNat ≤ psLen s + 128 := hp.rl

theorem sp1' (hp : RPre s) : frameBytes ≤ s.sp.toNat := by have := hp.sp1; unfold frameBytes; omega

theorem fb_ge (hp : RPre s) : 2176 ≤ (fb s).toNat := by
  have := fb_toNat (sp1' hp); have := hp.sp1; unfold frameBytes at *; omega

theorem kR_sub : Region.Sub (kR s) (stR s) :=
  Offset.sub_below s.sp (a := frameBytes) (b := 4304) (n := frameBytes) (m := 4304) (by decide) (by decide)

theorem lowR_sub : Region.Sub (lowR s) (stR s) := Region.sub_prefix (by decide)

theorem fb_sub48 : fb s - BitVec.ofNat 64 48 = s.sp - BitVec.ofNat 64 2176 := by
  rw [fb, BitVec.sub_sub, BitVec.ofNat_add_ofNat]; rfl

theorem low_eq : s.sp - BitVec.ofNat 64 2176 - BitVec.ofNat 64 2128 = s.sp - BitVec.ofNat 64 4304 := by
  rw [BitVec.sub_sub, BitVec.ofNat_add_ofNat]

theorem cR_sub : Region.Sub (cR s) (lowR s) := by
  rw [cR, fb_sub48]
  exact Offset.sub_below s.sp (a := 2176) (b := 4304) (n := 48) (m := 2176) (by decide) (by decide)

/-- A region apart from the stack is apart from our frame and from what is below it. -/
theorem k_dis {R : Region} (h : (stR s).Disjoint R) : (kR s).Disjoint R := h.sub_left kR_sub

theorem low_dis {R : Region} (h : (stR s).Disjoint R) : (lowR s).Disjoint R := h.sub_left lowR_sub

/-- Our frame and what is below it. -/
theorem kR_lowR (hp : RPre s) : (kR s).Disjoint (lowR s) := by
  have := hp.sp1
  have e : fb s = s.sp - BitVec.ofNat 64 4304 + BitVec.ofNat 64 2176 := by
    show s.sp - BitVec.ofNat 64 2128 = _
    rw [Offset.sub_ofNat_eq s.sp (show 2128 ≤ 4304 by decide)]
  rw [kR, e]
  exact Offset.disjoint_base _ (by decide) (by unfold frameBytes; omega)

theorem in_a7R {j : Nat} (hj : j < 7) : (a7R s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)

theorem arg_rd (hp : RPre s) (rs : List Region) {j : Nat} (hj : j < 7) :
    InRegions (s.rd ++ rs) (stackArgAddr s j) 8 :=
  ⟨a7R s, List.mem_append_left _ (by rw [hp.hrd]; simp), in_a7R hj⟩

/-- A stack argument, in memory changed only in the stack and the writable
buffers. -/
theorem arg_mem (hp : RPre s) {m : Mem} (h : Frame [kR s, tR s, oR s, scR s, lowR s] s.mem m) {j : Nat}
    (hj : j < 7) : m.readW (stackArgAddr s j) 64 = stackArg s j :=
  h.readW (in_a7R hj) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact (k_dis hp.ka).symm
    · exact hp.ta.symm
    · exact hp.oa.symm
    · exact hp.sa.symm
    · exact (low_dis hp.ka).symm) (by decide)

/-- The bytes of a buffer apart from the stack and the writable buffers. -/
theorem bytes_mem {m : Mem} (hf : Frame [kR s, tR s, oR s, scR s, lowR s] s.mem m) {R : Region}
    (hk : (kR s).Disjoint R) (ht : (tR s).Disjoint R) (ho : (oR s).Disjoint R) (hs : (scR s).Disjoint R)
    (hl' : (lowR s).Disjoint R) (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => hf.bytes (R := R) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hk.symm
  · exact ht.symm
  · exact ho.symm
  · exact hs.symm
  · exact hl'.symm

theorem words_mem {m : Mem} (hf : Frame [kR s, tR s, oR s, scR s, lowR s] s.mem m) {p : Addr} {n : Nat}
    (hk : (kR s).Disjoint ⟨p, n * 8⟩) (ht : (tR s).Disjoint ⟨p, n * 8⟩) (ho : (oR s).Disjoint ⟨p, n * 8⟩)
    (hs : (scR s).Disjoint ⟨p, n * 8⟩) (hl' : (lowR s).Disjoint ⟨p, n * 8⟩) (hw : p.toNat + n * 8 ≤ 2 ^ 64) :
    Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt s.mem p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => hf.readW (r := ⟨p, n * 8⟩) ?_ (fun r hr => ?_) (by decide)
  · have := List.mem_range.mp hi
    exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hk.symm
    · exact ht.symm
    · exact ho.symm
    · exact hs.symm
    · exact hl'.symm

theorem randB_length (s : State) : (randB s).length = (stackArg s 2).toNat := by
  simp [randB, Spec.Rsa.bytesAt]

theorem randB_getD {i : Nat} (hi : i < (stackArg s 2).toNat) :
    (randB s).getD i 0 = s.mem (stackArg s 1 + BitVec.ofNat 64 i) := by
  simp [randB, Spec.Rsa.bytesAt, hi]

end

open VG.WriteBytes

/-! ## Arithmetic -/

theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
  · intro h; rw [h]

theorem sub_ne_zero {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b != 0) = decide (a ≠ b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h e; exact h (by rw [e]; exact BitVec.sub_self _)
  · intro h e
    apply h
    have e' : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by
      rw [← BitVec.sub_add_cancel (BitVec.ofNat 64 a) (BitVec.ofNat 64 b), e]; exact BitVec.zero_add _
    have := congrArg BitVec.toNat e'
    simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

theorem ofNat_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    decide (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem nz_setWidth (b : Byte) : (b.setWidth 64 != 0) = !decide (b = 0) := by
  have := @Enc.setWidth_eq_zero b
  by_cases h : b = 0
  · simp [h]
  · have h' : b.setWidth 64 ≠ 0 := fun e => h (this.mp e)
    rw [bne_iff_ne.mpr h', decide_eq_false h]; rfl

/-! ## In the frame -/

/-- The regions the function writes. -/
abbrev W (s : State) : List Region := [kR s, tR s, oR s, scR s, lowR s]

/-- The slots of the saves. -/
abbrev svR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oSave, 40⟩

/-- In the frame: what the restores need, and memory changed only in the
regions the function writes. -/
structure InF (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = kR s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  sv : Spill.Saved (fb s) s.gpr saved t.mem
  fr : Frame (W s) s.mem t.mem

theorem InF.saves {s t : State} (h : InF s t) : Saves s t := ⟨h.sp, h.wr, h.hi, h.sv⟩

/-- A region the function may write, apart from the slots. -/
def Wok (s : State) (r : Region) : Prop := (∃ r' ∈ W s, Region.Sub r r') ∧ (svR s).Disjoint r

/-- `InF` is kept by writes of registers other than the callee-saved ones
and of memory the function may write, apart from the slots. -/
theorem InF.step {s t w : State} {rs : List Reg} (h : InF s t) (o : Kept rs t w) {R : List Region}
    (hm : Frame R t.mem w.mem) (hR : ∀ r ∈ R, Wok s r) (hrs : ∀ r ∈ rs, r ∉ hiRegs := by decide) : InF s w where
  sp := o.sp.trans h.sp
  rd := o.rd.trans h.rd
  wr := o.wr.trans h.wr
  hi := fun r hr => (o.gpr r fun h' => hrs r h' hr).trans (h.hi r hr)
  sv := h.sv.frame_in saved_offs hm fun r hr => (hR r hr).2
  fr := h.fr.trans (hm.sub fun r hr => (hR r hr).1)

theorem InF.only {s t w : State} {rs : List Reg} (h : InF s t) (o : Only rs t w)
    (hrs : ∀ r ∈ rs, r ∉ hiRegs := by decide) : InF s w :=
  h.step o.keep (R := []) (by rw [o.mem]; exact Frame.refl _ _) (fun _ h => nomatch h) hrs

/-- A write of the frame above the slots. -/
theorem wok_frame (s : State) {e n : Nat} (he : oRa + 8 ≤ e) (hen : e + n ≤ frameBytes) :
    Wok s ⟨fb s + BitVec.ofNat 64 e, n⟩ :=
  ⟨⟨kR s, List.mem_cons_self .., frame_sub s hen⟩,
    Offset.disjoint _ (.inl (by unfold oSave oRa at *; omega)) (by decide) (by unfold frameBytes at hen; omega)⟩

/-- A write of a region apart from the stack. -/
theorem wok_apart {s : State} {r : Region} (hr : r ∈ W s) (hd : (stR s).Disjoint r) : Wok s r :=
  ⟨⟨r, hr, fun _ h => h⟩, (k_dis hd).sub_left (frame_sub s (d := oSave) (n := 40) (by decide))⟩

theorem wok_low (s : State) (hp : RPre s) : Wok s (lowR s) :=
  ⟨⟨lowR s, by simp, fun _ h => h⟩, (kR_lowR hp).sub_left (frame_sub s (d := oSave) (n := 40) (by decide))⟩

end VG.Proof.RsaPkcs1Enc.RISCV64.Rnd
