module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCorrect
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.RISCV64.Keep
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.Contract
meta import VerifiedGarbage.Proof.Rsa.Contract

/-! ### `Rsa.RISCV64.PrivPre`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_private_checked` on RISC-V: the precondition

`PreP pc s`: the shared contract's precondition (`privateCheckedContract`, with
the stack of the frame, `frameBytes`), by name (`preP_of`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv

theorem stackArgs_twelve (s : State) :
    List.map (stackArg s) (List.range 12) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9, stackArg s 10,
      stackArg s 11] := rfl

/-! ## The buffers -/

abbrev oR (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev nR (s : State) : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
abbrev eR (s : State) : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
abbrev iR (s : State) : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
abbrev pR (s : State) : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
abbrev qR (s : State) : Region := ⟨stackArg s 2, (stackArg s 3).toNat⟩
abbrev dpR (s : State) : Region := ⟨stackArg s 4, (stackArg s 5).toNat⟩
abbrev dqR (s : State) : Region := ⟨stackArg s 6, (stackArg s 7).toNat⟩
abbrev qiR (s : State) : Region := ⟨stackArg s 8, (stackArg s 9).toNat⟩
abbrev sR (s : State) : Region := ⟨stackArg s 10, (stackArg s 11).toNat * 8⟩
/-- The stack arguments: 12, or with `pc` (`vg_rsa_private_checked_precomputed`) 14. -/
abbrev aR (pc : Bool) (s : State) : Region := ⟨stackArgAddr s 0, if pc then 112 else 96⟩
/-- With `pc`, the key's precomputed values, `pre_len` words. -/
abbrev preR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩

/-- The buffers the function reads. -/
abbrev rdL (pc : Bool) (s : State) : List Region :=
  [nR s, eR s, iR s, pR s, qR s, dpR s, dqR s, qiR s] ++ (if pc then [preR s] else []) ++ [aR pc s]

/-- The frame's base: the stack pointer in the frame. -/
abbrev fb (s : State) : Addr := s.sp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses: the frame. -/
abbrev kR (s : State) : Region := ⟨fb s, frameBytes⟩

/-- What the code needs of `privateCheckedContract.pre`, by name. -/
structure PreP (pc : Bool) (s : State) : Prop where
  sp16 : s.sp.toNat % 16 = 0
  sp1 : frameBytes ≤ s.sp.toNat
  sp2 : s.sp.toNat + 96 ≤ 2 ^ 64
  hrd : s.rd = rdL pc s
  hwr : s.wr = [oR s, sR s]
  on : (oR s).Disjoint (nR s)
  oe : (oR s).Disjoint (eR s)
  oi : (oR s).Disjoint (iR s)
  op : (oR s).Disjoint (pR s)
  oq : (oR s).Disjoint (qR s)
  odp : (oR s).Disjoint (dpR s)
  odq : (oR s).Disjoint (dqR s)
  oqi : (oR s).Disjoint (qiR s)
  os : (oR s).Disjoint (sR s)
  oa : (oR s).Disjoint (aR pc s)
  ns : (nR s).Disjoint (sR s)
  es : (eR s).Disjoint (sR s)
  is : (iR s).Disjoint (sR s)
  ps : (pR s).Disjoint (sR s)
  qs : (qR s).Disjoint (sR s)
  dps : (dpR s).Disjoint (sR s)
  dqs : (dqR s).Disjoint (sR s)
  qis : (qiR s).Disjoint (sR s)
  sa : (sR s).Disjoint (aR pc s)
  ko : (kR s).Disjoint (oR s)
  kn : (kR s).Disjoint (nR s)
  ke : (kR s).Disjoint (eR s)
  ki : (kR s).Disjoint (iR s)
  kp : (kR s).Disjoint (pR s)
  kq : (kR s).Disjoint (qR s)
  kdp : (kR s).Disjoint (dpR s)
  kdq : (kR s).Disjoint (dqR s)
  kqi : (kR s).Disjoint (qiR s)
  ks : (kR s).Disjoint (sR s)
  ka : (kR s).Disjoint (aR pc s)
  wo : (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64
  wn : (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64
  we : (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64
  wi : (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64
  wp : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wq : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wdp : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wdq : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wqi : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  ws : (stackArg s 10).toNat + (stackArg s 11).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .a3).toNat
  k2 : (s.gpr .a3).toNat ≤ 1024
  h1 : (s.gpr .a1).toNat = (s.gpr .a3).toNat
  h7 : (s.gpr .a7).toNat = (s.gpr .a3).toNat
  e1 : 1 ≤ (s.gpr .a5).toNat
  e2 : (s.gpr .a5).toNat ≤ (s.gpr .a3).toNat
  p1 : 1 ≤ (stackArg s 1).toNat
  p2 : (stackArg s 1).toNat < (s.gpr .a3).toNat
  q1 : 1 ≤ (stackArg s 3).toNat
  q2 : (stackArg s 3).toNat < (s.gpr .a3).toNat
  h5 : (stackArg s 5).toNat = (stackArg s 1).toNat
  h9 : (stackArg s 9).toNat = (stackArg s 1).toNat
  h7' : (stackArg s 7).toNat = (stackArg s 3).toNat
  hs : Spec.Rsa.scratchWords (s.gpr .a3).toNat ≤ (stackArg s 11).toNat
  al : (stackArg s 10).toNat % 8 = 0

theorem preP_of {s : State} (h : (Proof.Rsa.privateCheckedContract RISCV64.abi frameBytes).pre s) : PreP false s := by
  have e : frameBytes = 3247 + 1 := rfl
  rw [e] at h
  sig_pre [Proof.Rsa.privateCheckedContract, Proof.Rsa.privateCheckedSig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_twelve, List.append_eq, List.range, List.range.loop] at h
  sig_split h
  rename_i sp16 sp1 sp2 hrd hwr on oe oi op oq odp odq oqi os oa ns es is ps qs dps dqs qis sa ko kn ke ki kp kq
    kdp kdq kqi ks ka wo wn we wi wp wq wdp wdq wqi ws h_k1_k2 h1 h7 e1 e2 p1 p2 q1 q2 h5 h9 h7' hs
  have al := h
  obtain ⟨k1, k2⟩ := h_k1_k2
  exact ⟨sp16, sp1, sp2, hrd, hwr, on, oe, oi, op, oq, odp, odq, oqi, os, oa, ns, es, is, ps, qs, dps, dqs, qis, sa,
    ko, kn, ke, ki, kp, kq, kdp, kdq, kqi, ks, ka, wo, wn, we, wi, wp, wq, wdp, wdq, wqi, ws, k1, k2, h1, h7, e1,
    e2, p1, p2, q1, q2, h5, h9, h7', hs, al⟩

end VG.Proof.Rsa.RISCV64.Priv

end

end

/-! ### `Rsa.RISCV64.PrivSetup`, which only this module used -/

section

/-!
# `vg_rsa_private_checked` on RISC-V: the frame, up to the call of `vg_rsa_private_crt`

The frame (`Impl/Rsa/RISCV64/Priv.lean`) is all of the stack the function
uses, `kR`, from its base `fb`, and is writable. From the state after its
`alloc`: the saves of `s1`–`s6` and of the return address, the values kept in
`s1`–`s6`, the call's arguments, and its ten stack arguments copied from ours
(`setup_ok`, into `AtCrt`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

variable {pc : Bool}

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

/-! ## Addresses -/

theorem fb_toNat {s : State} (h : frameBytes ≤ s.sp.toNat) : (fb s).toNat + frameBytes = s.sp.toNat := by
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_using [h]

theorem fb_al {s : State} (h : PreP pc s) : (fb s).toNat % 16 = 0 := by
  have := fb_toNat h.sp1; have := h.sp16; unfold frameBytes at *; omega_arith

/-- A word of the frame at an offset that is a multiple of 8 is aligned. -/
theorem fb_al8 {s : State} (h : PreP pc s) {d : Nat} (hd : d % 8 = 0) :
    (fb s + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  have := fb_toNat h.sp1; have := fb_al h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; unfold frameBytes at *; omega_using [hd, this]

/-- A region of the frame is in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    Region.Sub ⟨fb s + BitVec.ofNat 64 d, n⟩ (kR s) := Offset.sub_base _ h

theorem frame_contains (s : State) {d n : Nat} (h : d + n ≤ frameBytes) :
    (kR s).Contains (fb s + BitVec.ofNat 64 d) n :=
  Offset.contains_base _ h (by unfold frameBytes at h; omega_using [h])

/-- The frame is writable. -/
theorem in_fr (s : State) (rs : List Region) {d n : Nat} (h : d + n ≤ frameBytes) :
    InRegions (kR s :: rs) (fb s + BitVec.ofNat 64 d) n :=
  ⟨_, List.mem_cons_self .., frame_contains s h⟩

theorem stackArgAddr_eq (s : State) (j : Nat) :
    stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) := by
  simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]

theorem in_aR {s : State} {j : Nat} (hj : j < 12) : (aR pc s).Contains (stackArgAddr s j) 8 := by
  rw [stackArgAddr_eq s j]
  cases pc <;> exact Offset.contains_base _ (by simp only [Bool.false_eq_true, ↓reduceIte]; omega_using [hj]) (by omega_using [hj])

/-! ## The saves -/

/-- The slots of our caller's `s1`–`s6` and of the return address. -/
def saved : List (Reg × Nat) :=
  [(.s1, oSave), (.s2, oSave + 8), (.s3, oSave + 16), (.s4, oSave + 24), (.s5, oSave + 32),
    (.s6, oSave + 40), (.ra, oRa)]

/-- The restores, the return address first. -/
def restored : List (Reg × Nat) :=
  [(.ra, oRa), (.s1, oSave), (.s2, oSave + 8), (.s3, oSave + 16), (.s4, oSave + 24), (.s5, oSave + 32),
    (.s6, oSave + 40)]

/-- The callee-saved registers other than `s1`–`s6`. -/
def hiRegs : List Reg := [.s0, .s7, .s8, .s9, .s10, .s11]

/-- The moves to `s1`–`s6`. -/
abbrev movs : List Instr := [mov .s1 .a0, mov .s2 .a2, mov .s3 .a3, mov .s4 .a4, mov .s5 .a5, mov .s6 .a6]

theorem save_eq : save = ([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved ++ movs := rfl

theorem restore_eq : restore = ([.addSp .t0 0] : List Instr) ++ Spill.restoreCode .t0 restored := rfl

theorem saved_offs : ∀ p ∈ saved, oSave ≤ p.2 ∧ p.2 + 8 ≤ oSave + 56 := by decide

theorem saved_fits : Spill.Fits saved := by decide

theorem restored_offs : ∀ p ∈ restored, p.2 % 8 = 0 ∧ p.2 < 2048 := by decide

theorem restorable : Spill.Restorable .t0 restored := by decide

theorem restored_saved : ∀ p ∈ restored, p ∈ saved := by decide

theorem preserved_split {r : Reg} (h : r ∈ preserved) : r ∈ saved.map Prod.fst ∨ r ∈ hiRegs := by
  revert r; decide

/-- In the frame, from the entry state `s`: our caller's registers and
return address in their slots, the other callee-saved registers as on entry,
memory changed only in the stack the function uses. -/
structure Fr (s t : State) : Prop where
  sp : t.sp = fb s
  rd : t.rd = s.rd
  wr : t.wr = kR s :: s.wr
  hi : ∀ r ∈ hiRegs, t.gpr r = s.gpr r
  mem : Frame [kR s] s.mem t.mem
  sv : Spill.Saved (fb s) s.gpr saved t.mem

/-- The saves, from the state after the frame's `alloc`: `t0` holds the
frame's base, `s1`–`s6` and the return address are in their slots, and memory
is changed only in the frame. -/
theorem save_ok {s : State} (h : PreP pc s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ v, Fr s v → v.gpr .t0 = fb s → (∀ r, r ≠ .t0 → v.gpr r = s.gpr r) →
      WP isa (.block rest) v Q) :
    WP isa (.block (([.addSp .t0 0] : List Instr) ++ Spill.saveCode .t0 saved ++ rest))
      (allocd frameBytes s) Q := by
  simp only [List.cons_append, List.nil_append]
  refine WP.block_cons_iff.mpr ⟨_, exec_addSp (imm := 0) (by decide), ?_⟩
  generalize hu : (allocd frameBytes s).write .t0 ((allocd frameBytes s).sp + BitVec.ofNat 64 0) = u
  have u0 : u.gpr .t0 = fb s := by rw [← hu, gpr_write_self]; exact BitVec.add_zero _
  have ug : ∀ r, r ≠ .t0 → u.gpr r = s.gpr r := fun r hr => by
    rw [← hu, gpr_write_of_ne _ _ hr]; rfl
  have uwr : u.wr = kR s :: s.wr := by rw [← hu]; rfl
  refine Spill.save_ok (b := .t0) (l := saved) (by rw [u0]; have := fb_al h; omega_using [this])
    saved_fits.1 (fun p hp => ?_) ?_
  · have := saved_offs p hp
    rw [uwr, u0]; exact in_fr s _ (by unfold oSave frameBytes at *; omega_using [this])
  refine k _ ⟨?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩ ?_ fun r h0 => ?_
  · show u.sp = fb s; rw [← hu]; rfl
  · show u.rd = s.rd; rw [← hu]; rfl
  · exact uwr
  · exact ug r (by revert r; decide)
  · show Frame [kR s] s.mem (Spill.saveMem u.mem (u.gpr .t0) u.gpr saved)
    rw [u0, show u.mem = s.mem by rw [← hu]; rfl]
    exact Spill.saveMem_frame_base (fun p hp => by
      have := saved_offs p hp; unfold oSave frameBytes at *; omega_using [this]) (by decide) _ _ _
  · show Spill.Saved (fb s) s.gpr saved (Spill.saveMem u.mem (u.gpr .t0) u.gpr saved)
    rw [u0]
    refine fun p hp => (Spill.saveMem_saved saved_fits _ _ _ p hp).trans (ug _ ?_)
    revert p; decide
  · exact u0
  · exact ug r h0

/-! ## The stack arguments -/

theorem stackArgAddr_al {s : State} (h : PreP pc s) (j : Nat) :
    (stackArgAddr s j).toNat % 8 = 0 := by
  have := h.sp16; have := h.sp2
  simp only [stackArgAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

/-- Our stack argument `j` is in the arguments' region, apart from the frame. -/
theorem arg_read {s : State} (h : PreP pc s) {m : Mem} (hm : Frame [kR s] s.mem m) {j : Nat} (hj : j < 12) :
    m.readW (stackArgAddr s j) 64 = stackArg s j :=
  hm.readW (in_aR (pc := pc) hj) (fun r hr => by rw [List.mem_singleton.mp hr]; exact h.ka.symm) (by decide)

/-- Our stack argument `j`, after the frame and the working space changed. -/
theorem arg_read2 {s : State} (h : PreP pc s) {m : Mem} (hm : Frame [kR s, sR s] s.mem m) {j : Nat}
    (hj : j < 12) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine hm.readW (in_aR (pc := pc) hj) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.ka.symm
  · exact h.sa.symm

theorem arg_in {s t : State} (h : PreP pc s) (hrd : t.rd = s.rd) {j : Nat} (hj : j < 12) :
    InRegions (t.rd ++ t.wr) (stackArgAddr s j) 8 := by
  rw [hrd, h.hrd]
  exact ⟨aR pc s, List.mem_append_left _ (by simp), in_aR hj⟩

/-- `argBase`: `t6` holds the address of our first stack argument. -/
theorem argBase_ok {s v : State} (hsp : v.sp = fb s) {rest : List Instr} {Q : State → Prop}
    (k : ∀ w, w.gpr .t6 = s.sp → Keep [.t6] v w → w.mem = v.mem → w.sp = v.sp → WP isa (.block rest) w Q) :
    WP isa (.block (argBase ++ rest)) v Q := by
  simp only [argBase, List.cons_append, List.nil_append]
  have e1 := exec_addSp (s := v) (d := .t6) (imm := 2032) (by decide)
  have e2 := exec_addi_nat (s := v.write .t6 (v.sp + BitVec.ofNat 64 2032)) (d := .t6) (n := .t6)
    (m := frameBytes - 2032) (by unfold frameBytes; omega_using [])
  refine WP.block_cons_iff.mpr ⟨_, e1, WP.block_cons_iff.mpr ⟨_, e2, k _ ?_ ⟨fun r hr => ?_, rfl, rfl⟩ rfl rfl⟩⟩
  · rw [gpr_write_self, gpr_write_self, hsp, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
    exact BitVec.sub_add_cancel _ _
  · have : r ≠ .t6 := by simpa using hr
    rw [gpr_write_of_ne _ _ this, gpr_write_of_ne _ _ this]

/-! ## Up to the call -/

/-- The stack arguments of the calls, at the frame's base. -/
abbrev psaR (s : State) : Region := ⟨fb s, 80⟩

/-- At the call of `vg_rsa_private_crt`. -/
structure AtCrt (s t : State) : Prop extends Fr s t where
  a0 : t.gpr .a0 = fb s + BitVec.ofNat 64 oM
  a1 : t.gpr .a1 = s.gpr .a3
  a2 : t.gpr .a2 = s.gpr .a2
  a3 : t.gpr .a3 = s.gpr .a3
  a4 : t.gpr .a4 = s.gpr .a6
  a5 : t.gpr .a5 = s.gpr .a3
  a6 : t.gpr .a6 = stackArg s 0
  a7 : t.gpr .a7 = stackArg s 1
  s1 : t.gpr .s1 = s.gpr .a0
  s2 : t.gpr .s2 = s.gpr .a2
  s3 : t.gpr .s3 = s.gpr .a3
  s4 : t.gpr .s4 = s.gpr .a4
  s5 : t.gpr .s5 = s.gpr .a5
  s6 : t.gpr .s6 = s.gpr .a6
  psa : ∀ i < 10, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i)

/-- After copying the first `n` stack arguments, from `w`. -/
structure CI (s w : State) (n : Nat) (t : State) : Prop where
  keep : Keep [.t1] w t
  mem : Frame [psaR s] w.mem t.mem
  psa : ∀ i < n, t.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i)

theorem copy_step {s w : State} (h : PreP pc s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = s.sp)
    (hrd : w.rd = s.rd) (hwr : w.wr = kR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) {n : Nat} (hn : n < 10)
    {t : State} (hc : CI s w n t) : WP isa (.block (argCopy n)) t (CI s w (n + 1)) := by
  have t0 : t.gpr .t0 = fb s := (hc.keep.gpr (by decide)).trans hw0
  have t6 : t.gpr .t6 = s.sp := (hc.keep.gpr (by decide)).trans hw6
  have psa_sub : Region.Sub (psaR s) (kR s) := by
    have := frame_sub s (d := 0) (n := 80) (by decide); rwa [BitVec.add_zero] at this
  have hmt : Frame [kR s] s.mem t.mem := hm.trans (hc.mem.sub fun r hr => by
    rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩)
  have ea : t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n)) = stackArgAddr s (2 + n) := by rw [t6]; rfl
  have hin : InRegions (t.rd ++ t.wr) (t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n))) 8 := by
    rw [ea]; exact arg_in h (hc.keep.2.1.trans hrd) (by omega_using [hn])
  have hv : t.mem.readW (t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n))) 64 = stackArg s (2 + n) := by
    rw [ea]; exact arg_read h hmt (by omega_using [hn])
  have hal : (t.gpr .t6 + BitVec.ofNat 64 (8 * (2 + n))).toNat % 8 = 0 := by
    rw [ea]; exact stackArgAddr_al h _
  have ho : InRegions t.wr (t.gpr .t0 + BitVec.ofNat 64 (8 * n)) 8 := by
    rw [t0, hc.keep.2.2, hwr]; exact in_fr s _ (by unfold frameBytes; omega_using [hn])
  apply WP.of_runBlock
  simp only [argCopy, runBlock_cons, runStep_some, exec_load_d (by omega_using [hn]) hal hin]
  rw [exec_store_d (by omega_using [hn]) (by rw [gpr_write_of_ne _ _ (by decide), t0]; exact fb_al8 h (by omega_using []))
    (by rw [gpr_write_of_ne _ _ (show Reg.t0 ≠ .t1 by decide)]; exact ho)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left']
  rw [gpr_write_of_ne _ _ (show Reg.t0 ≠ .t1 by decide), gpr_write_self, mem_write, hv, t0]
  refine ⟨⟨fun r hr => ?_, hc.keep.2.1, hc.keep.2.2⟩, ?_, fun i hi => ?_⟩
  · show (t.write .t1 _).gpr r = w.gpr r
    rw [gpr_write_of_ne _ _ (by simpa using hr)]; exact hc.keep.gpr hr
  · exact hc.mem.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep _ (.inl (by omega_using [hi])) (by omega_arith) (by omega_using [hn])) (by decide)]
      exact hc.psa i hi
    · rw [Mem.readW_writeW_self64]

theorem copies_ok {s w : State} (h : PreP pc s) (hw0 : w.gpr .t0 = fb s) (hw6 : w.gpr .t6 = s.sp)
    (hrd : w.rd = s.rd) (hwr : w.wr = kR s :: s.wr) (hm : Frame [kR s] s.mem w.mem) :
    WP isa (.block ((List.range 10).flatMap argCopy)) w (CI s w 10) :=
  wp_range_flatMap (M := isa) (CI s w) (fun _ _ hn hc => copy_step h hw0 hw6 hrd hwr hm hn hc) 10
    (Nat.le_refl _) w ⟨Keep.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- `crtArgs` after `argBase`: the arguments in registers. -/
abbrev crtHead : List Instr :=
  [.addi .a0 .t0 oM, mov .a1 .s3, mov .a4 .s6, mov .a5 .s3, .load .d .a6 .t6 0, .load .d .a7 .t6 8]

theorem crtArgs_eq : crtArgs = argBase ++ (crtHead ++ (List.range 10).flatMap argCopy) := by
  simp only [crtArgs, List.append_assoc]

theorem movs_ok {s v : State} (hg : ∀ r, r ≠ .t0 → v.gpr r = s.gpr r) :
    WP isa (.block movs) v fun w =>
      (w.gpr .s1 = s.gpr .a0 ∧ w.gpr .s2 = s.gpr .a2 ∧ w.gpr .s3 = s.gpr .a3 ∧ w.gpr .s4 = s.gpr .a4 ∧
        w.gpr .s5 = s.gpr .a5 ∧ w.gpr .s6 = s.gpr .a6 ∧ w.mem = v.mem) ∧
      Keep [.s1, .s2, .s3, .s4, .s5, .s6] v w := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, hg .a0 (by decide), hg .a2 (by decide), hg .a3 (by decide), hg .a4 (by decide),
    hg .a5 (by decide), hg .a6 (by decide), BitVec.add_zero]

theorem head_ok {s w : State} (h : PreP pc s) (hrd : w.rd = s.rd) (hm : Frame [kR s] s.mem w.mem)
    (h0 : w.gpr .t0 = fb s) (h6 : w.gpr .t6 = s.sp) (h3 : w.gpr .s3 = s.gpr .a3)
    (h6' : w.gpr .s6 = s.gpr .a6) :
    WP isa (.block crtHead) w fun u =>
      (u.gpr .a0 = fb s + BitVec.ofNat 64 oM ∧ u.gpr .a1 = s.gpr .a3 ∧ u.gpr .a4 = s.gpr .a6 ∧
        u.gpr .a5 = s.gpr .a3 ∧ u.gpr .a6 = stackArg s 0 ∧ u.gpr .a7 = stackArg s 1 ∧ u.mem = w.mem) ∧
      Keep [.a0, .a1, .a4, .a5, .a6, .a7] w u := by
  have i0 : InRegions (w.rd ++ w.wr) (s.sp + BitVec.ofNat 64 0) 8 := arg_in h hrd (j := 0) (by decide)
  have i1 : InRegions (w.rd ++ w.wr) (s.sp + BitVec.ofNat 64 8) 8 := arg_in h hrd (j := 1) (by decide)
  have l0 : (s.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := stackArgAddr_al h 0
  have l1 : (s.sp + BitVec.ofNat 64 8).toNat % 8 = 0 := stackArgAddr_al h 1
  have r0 : w.mem.readW (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := arg_read h hm (j := 0) (by decide)
  have r1 : w.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := arg_read h hm (j := 1) (by decide)
  simp only [BitVec.add_zero] at i0 l0 r0
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [mov, h0, h6, h3, h6', i0, i1, l0, l1, r0, r1, BitVec.add_zero, oM]

theorem setup_core {s : State} (h : PreP pc s) :
    WP isa (.block (save ++ crtArgs)) (allocd frameBytes s) fun t => t.sp = fb s → AtCrt s t := by
  rw [save_eq, crtArgs_eq, List.append_assoc]
  refine save_ok h fun v F h0 hg => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.rdwr (movs_ok hg)) fun w ⟨⟨⟨w1, w2, w3, w4, w5, w6, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  have w0 : w.gpr .t0 = fb s := (kw.gpr (by decide)).trans h0
  refine argBase_ok (s := s) (wsp.trans F.sp) fun x x6 kx xm _ => ?_
  have x0 : x.gpr .t0 = fb s := (kx.gpr (by decide)).trans w0
  have xrd : x.rd = s.rd := kx.2.1.trans (wrd.trans F.rd)
  have xwr : x.wr = kR s :: s.wr := kx.2.2.trans (wwr.trans F.wr)
  have xm' : Frame [kR s] s.mem x.mem := by rw [xm, wm]; exact F.mem
  rw [WP.block_append_iff]
  refine WP.mono (head_ok h xrd xm' x0 x6 ((kx.gpr (by decide)).trans w3) ((kx.gpr (by decide)).trans w6))
    fun y ⟨⟨y0, y1, y4, y5, y6, y7, ym⟩, ky⟩ => ?_
  refine WP.mono (copies_ok h ((ky.gpr (by decide)).trans x0) ((ky.gpr (by decide)).trans x6)
    (ky.2.1.trans xrd) (ky.2.2.trans xwr) (by rw [ym]; exact xm')) fun t hc tsp => ?_
  have k := hc.keep
  have psa_sub : Region.Sub (psaR s) (kR s) := by
    have := frame_sub s (d := 0) (n := 80) (by decide); rwa [BitVec.add_zero] at this
  have hsv : Spill.Saved (fb s) s.gpr saved y.mem := by rw [ym, xm, wm]; exact F.sv
  have g : ∀ r, r ∉ ([.t1, .a0, .a1, .a4, .a5, .a6, .a7] : List Reg) → t.gpr r = x.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [k.gpr (by simp [hr.1]), ky.gpr (by simp [hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2])]
  refine ⟨⟨tsp, k.2.1.trans (ky.2.1.trans xrd), k.2.2.trans (ky.2.2.trans xwr), fun r hr => ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.psa⟩
  · rw [g r (by revert r; decide), kx.gpr (by revert r; decide), kw.gpr (by revert r; decide)]
    exact F.hi r hr
  · rw [← ym] at xm'
    exact xm'.trans (hc.mem.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨_, List.mem_singleton_self _, psa_sub⟩)
  · exact hsv.frame hc.mem fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      exact Offset.disjoint_base _ (by unfold oSave at this; omega_using [this]) (by unfold oSave at this; omega_using [this])
  · rw [k.gpr (by decide)]; exact y0
  · rw [k.gpr (by decide)]; exact y1
  · rw [g _ (by decide), kx.gpr (by decide), kw.gpr (by decide)]; exact hg _ (by decide)
  · rw [g _ (by decide), kx.gpr (by decide), kw.gpr (by decide)]; exact hg _ (by decide)
  · rw [k.gpr (by decide)]; exact y4
  · rw [k.gpr (by decide)]; exact y5
  · rw [k.gpr (by decide)]; exact y6
  · rw [k.gpr (by decide)]; exact y7
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w1
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w2
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w3
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w4
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w5
  · rw [g _ (by decide), kx.gpr (by decide)]; exact w6

theorem setup_ok {s : State} (h : PreP pc s) :
    WP isa (.block (save ++ crtArgs)) (allocd frameBytes s) (AtCrt s) :=
  WP.mono (WP.rdwr (setup_core h)) fun _ ⟨hc, _, _, hsp⟩ => hc hsp

/-- Between the calls, from the entry state `s`: the frame, the values kept
in `s1`–`s6`, the other callee-saved registers as on entry, our caller's
registers and return address in their slots, and memory changed only in the
frame and the working space. -/
structure Mid (s u : State) : Prop where
  sp : u.sp = fb s
  rd : u.rd = s.rd
  wr : u.wr = kR s :: s.wr
  s1 : u.gpr .s1 = s.gpr .a0
  s2 : u.gpr .s2 = s.gpr .a2
  s3 : u.gpr .s3 = s.gpr .a3
  s4 : u.gpr .s4 = s.gpr .a4
  s5 : u.gpr .s5 = s.gpr .a5
  s6 : u.gpr .s6 = s.gpr .a6
  hi : ∀ r ∈ hiRegs, u.gpr r = s.gpr r
  mem : Frame [kR s, sR s] s.mem u.mem
  sv : Spill.Saved (fb s) s.gpr saved u.mem

/-- A buffer of the caller that the function does not write. -/
theorem bytes_of_frame {s : State} {rs : List Region} {m : Mem} (hf : Frame rs s.mem m) {p : Addr}
    {len : Nat} (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, len⟩ r) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, len⟩) hd hl (List.mem_range.mp hi)

end VG.Proof.Rsa.RISCV64.Priv

end

end

/-!
# `vg_rsa_private_checked` on RISC-V: the calls of `vg_rsa_private_crt` and `vg_rsa_public_precompute`

By the first callee's contract on its registers and stack (`Crt.fnContract`,
`Crt.fn_correct`): the regions it is narrowed to (`crtRd`, `crtWr`), its
precondition at the call (`crt_pre`), and the call (`crtCall_ok`). Then the
CRT's status kept in the frame (`preArgs_ok`, into `AtPre`), and the call
by the second callee's contract on its registers (`Pre.fnContract`,
`Pre.fn_correct`): `n`'s values into the frame (`preCall_ok`).
-/

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.Priv

variable {pc : Bool}

open VG VG.RISCV64 VG.Impl.Rsa.RISCV64.Priv VG.RISCV64.RegUpd

/-! ## The call of `vg_rsa_private_crt` -/

/-- `m`, in the frame. -/
abbrev mR (s : State) : Region := ⟨fb s + BitVec.ofNat 64 oM, (s.gpr .a3).toNat⟩

/-- The regions the call reads and writes. -/
abbrev crtRd (s : State) : List Region :=
  [nR s, ⟨s.gpr .a6, (s.gpr .a3).toNat⟩, pR s, qR s, dpR s, dqR s, qiR s, psaR s]

abbrev crtWr (s : State) : List Region := [mR s, sR s]

/-- The call's narrowed entry state. -/
abbrev crtEntry (s t : State) : State := t.callEntry.withRegions (crtRd s) (crtWr s)

/-- The narrowed entry state of a call from `u`, with the regions `X` read
too. -/
abbrev crtEntryG (s u : State) (X : List Region) : State := u.callEntry.withRegions (crtRd s ++ X) (crtWr s)

theorem crtEntryG_stackArg {s t u : State} (A : AtCrt s t)
    (hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i))
    (hsp : u.sp = t.sp) {X : List Region} {i : Nat} (hi : i < 10) :
    stackArg (crtEntryG s u X) i = stackArg s (2 + i) := by
  show u.mem.readW ((crtEntryG s u X).sp + BitVec.ofNat 64 (8 * i)) 64 = _
  rw [show (crtEntryG s u X).sp = fb s from hsp.trans A.sp]
  exact hpsa i hi

theorem crtEntry_stackArg {s t : State} (A : AtCrt s t) {i : Nat} (hi : i < 10) :
    stackArg (crtEntry s t) i = stackArg s (2 + i) := by
  show t.mem.readW ((crtEntry s t).sp + BitVec.ofNat 64 (8 * i)) 64 = _
  rw [show (crtEntry s t).sp = fb s from A.sp]
  exact A.psa i hi

theorem psa_sub (s : State) : Region.Sub (psaR s) (kR s) := by
  have := frame_sub s (d := 0) (n := 80) (by decide); rwa [BitVec.add_zero] at this

theorem mR_sub {s : State} (h : PreP pc s) : Region.Sub (mR s) (kR s) :=
  frame_sub s (by have := h.k2; unfold oM frameBytes; omega_using [this])

theorem iR_eq {s : State} (h : PreP pc s) : (⟨s.gpr .a6, (s.gpr .a3).toNat⟩ : Region) = iR s := by
  simp only [iR, h.h7]

/-- `vg_rsa_private_crt`'s precondition but its regions, at the call from `u`
(with `t`'s arguments), with the regions `X` read too. -/
theorem crt_preG {s t u : State} (h : PreP pc s) (A : AtCrt s t)
    (k : ∀ r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7], u.gpr r = t.gpr r)
    (hpsa : ∀ i < 10, u.mem.readW (fb s + BitVec.ofNat 64 (8 * i)) 64 = stackArg s (2 + i))
    (hsp : u.sp = t.sp) {X : List Region} :
    Proof.Bignum.RISCV64.Crt.preCore (Proof.Bignum.RISCV64.Crt.baseRd (crtEntryG s u X) ++ X)
      (crtEntryG s u X) := by
  have g : ∀ r, r ∉ linkRegs → r ∈ [Reg.a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7] →
      (crtEntryG s u X).gpr r = t.gpr r := fun r h1 h2 => (State.callEntry_gpr u h1).trans (k r h2)
  have sa := fun i hi => crtEntryG_stackArg A hpsa hsp (X := X) (i := i) hi
  have hsp' : (crtEntryG s u X).sp = fb s := hsp.trans A.sp
  have ha : stackArgAddr (crtEntryG s u X) 0 = fb s := by
    simp only [stackArgAddr, hsp', Nat.mul_zero, BitVec.add_zero]
  simp only [Proof.Bignum.RISCV64.Crt.preCore, Proof.Bignum.RISCV64.Crt.baseRd,
    Proof.Bignum.RISCV64.Crt.stackArgs, g .a0 (by decide) (by decide), g .a1 (by decide) (by decide), g .a2 (by decide) (by decide),
    g .a3 (by decide) (by decide), g .a4 (by decide) (by decide), g .a5 (by decide) (by decide),
    g .a6 (by decide) (by decide), g .a7 (by decide) (by decide), A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, A.a6, A.a7,
    sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 3 (by decide), sa 4 (by decide), sa 5 (by decide),
    sa 6 (by decide), sa 7 (by decide), sa 8 (by decide), sa 9 (by decide), hsp', ha, State.withRegions_rd,
    State.withRegions_wr, Nat.reduceAdd]
  have hk := h.k2
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have mk := mR_sub h
  have pk := psa_sub s
  have mp : (mR s).Disjoint (psaR s) := Offset.disjoint_base _ (by decide) (by unfold oM; omega_using [hk])
  rw [iR_eq h]
  refine ⟨trivial, trivial, h.kn.sub_left mk, h.ki.sub_left mk, h.kp.sub_left mk, h.kq.sub_left mk,
    h.kdp.sub_left mk, h.kdq.sub_left mk, h.kqi.sub_left mk, h.ks.sub_left mk, mp, h.ns, h.is, h.ps, h.qs,
    h.dps, h.dqs, h.qis, (h.ks.sub_left pk).symm, ?_, h.wn, by rw [← h.h7]; exact h.wi, h.wp, h.wq, h.wdp,
    h.wdq, h.wqi, h.ws, ⟨h.k1, h.k2⟩, trivial, trivial, h.p1, h.p2, h.q1, h.q2, h.h5, h.h9, h.h7', h.hs, h.al,
    fb_al h⟩
  · rw [Offset.toNat_add_ofNat]; unfold oM at *; omega_using [hk, fbt]

theorem crt_pre {s t : State} (h : PreP pc s) (A : AtCrt s t) :
    Proof.Bignum.RISCV64.Crt.fnContract.pre (crtEntry s t) := by
  have := crt_preG (X := []) h A (fun _ _ => rfl) A.psa rfl
  simp only [List.append_nil] at this
  exact this

/-- The bytes of `m` after the call: `vg_rsa_private_crt`'s result for the
caller's buffers, and its status. -/
abbrev crtOut (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat ((u.gpr .a0).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- The frame below `m` is apart from what the call writes. -/
theorem below_apart {s : State} (h : PreP pc s) {d : Nat} (hd : d + 8 ≤ oM) {r : Region} (hr : r ∈ crtWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, 8⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl hd) (by unfold oM at hd; omega_using [hd]) (by have := h.k2; unfold oM; omega_using [this])
  · exact h.ks.sub_left (frame_sub s (by unfold oM frameBytes at *; omega_using [hd]))

theorem crt_noFrames : Impl.Bignum.RISCV64.Crt.crt.noFrames = true := by decide +kernel

theorem crt_covers {s t : State} (h : PreP pc s) (A : AtCrt s t) :
    Covers (crtRd s ++ crtWr s) (t.rd ++ t.wr) ∧ Covers (crtWr s) t.wr := by
  have hk := h.k2
  have hw : Covers (crtWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oM frameBytes; omega_using [hk]))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  refine ⟨Covers.append_left (Covers.of_forall fun r hr => ?_) (Covers.right hw), hw⟩
  rw [A.rd, A.wr, h.hrd]
  simp only [crtRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_left 7
  · exact Covers.right (Covers.of_sub fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, List.mem_cons_self .., 0, (BitVec.add_zero _).symm, show 0 + 80 ≤ frameBytes by unfold frameBytes; omega_using []⟩)
  all_goals exact Covers.left (Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp [iR_eq h])

theorem crtCall_ok {s t : State} (h : PreP pc s) (A : AtCrt s t) {Q : State → Prop}
    (hQ : ∀ u, Mid s u → crtOut s u → Q u) : WP isa crtCall t Q := by
  have mk := mR_sub h
  obtain ⟨hc, hw⟩ := crt_covers h A
  unfold crtCall
  refine WP.call (k := Proof.Bignum.RISCV64.Crt.fnContract) Proof.Bignum.RISCV64.Crt.fn_correct (crt_pre h A) hc
    hw (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_ ?_) crt_noFrames
  · have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
    refine ⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.s1,
      (hp _ (by decide)).trans A.s2, (hp _ (by decide)).trans A.s3, (hp _ (by decide)).trans A.s4,
      (hp _ (by decide)).trans A.s5, (hp _ (by decide)).trans A.s6,
      fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ?_, A.sv.frame hf fun p hp' r hr => below_apart h (by
        have := saved_offs p hp'; unfold oSave oM at *; omega_using [this]) hr⟩
    refine (A.mem.mono fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; exact List.mem_cons_self ..
    · simp only [crtWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., mk⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  · have g : ∀ r, r ∉ linkRegs → (crtEntry s t).gpr r = t.gpr r := fun r hr => State.callEntry_gpr t hr
    have sa := fun i hi => crtEntry_stackArg A (i := i) hi
    simp only [Proof.Bignum.RISCV64.Crt.fnContract, Proof.Bignum.RISCV64.Crt.postCore, g .a0 (by decide),
      g .a2 (by decide), g .a3 (by decide),
      g .a4 (by decide), g .a6 (by decide), g .a7 (by decide), A.a0, A.a2, A.a3, A.a4, A.a6, A.a7,
      sa 0 (by decide), sa 1 (by decide), sa 2 (by decide), sa 4 (by decide), sa 6 (by decide),
      State.withRegions_mem, State.withRegions_gpr, State.callEntry_mem, Nat.reduceAdd] at hpost
    have hb := fun {p : Addr} {len : Nat} (hd : Region.Disjoint ⟨p, len⟩ (kR s)) (hl : len ≤ 2 ^ 64) =>
      bytes_of_frame (s := s) (rs := [kR s]) A.mem (p := p) (len := len)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hl
    rw [hb h.kn.symm (by have := h.wn; omega_using []), hb (iR_eq h ▸ h.ki.symm) (by have := h.k2; omega_using []),
      hb h.kp.symm (by have := h.wp; omega_using []), hb h.kq.symm (by have := h.wq; omega_using []),
      hb (h.h5 ▸ h.kdp.symm) (by have := h.wdp; omega_using []), hb (h.h7' ▸ h.kdq.symm) (by have := h.wdq; omega_using []),
      hb (h.h9 ▸ h.kqi.symm) (by have := h.wqi; omega_using [])] at hpost
    exact hpost

/-! ## The call of `vg_rsa_public_precompute` -/

theorem written_congr {m m' : Mem} {out : Addr} {k : Nat} {r : BitVec 32} {o : Option (List Byte)}
    (hb : Spec.Rsa.bytesAt m' out k = Spec.Rsa.bytesAt m out k) (h : Spec.Rsa.written m out k r o) :
    Spec.Rsa.written m' out k r o := by
  cases o <;> simp only [Spec.Rsa.written, hb] at h ⊢ <;> exact h

/-- `m` and the CRT's status kept in the frame. -/
abbrev crtOutM (s u : State) : Prop :=
  Spec.Rsa.written u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat
    ((u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64).setWidth 32)
    (Spec.Rsa.privateCrt (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 4) (stackArg s 1).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 6) (stackArg s 3).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 8) (stackArg s 1).toNat))

/-- `Mid` is kept by a write of a word of the frame apart from the slots. -/
theorem Mid.store {s t : State} (M : Mid s t) {d : Nat} (hd : oRa + 8 ≤ d ∨ d + 8 ≤ oSave)
    (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Mid s u := by
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.s1,
    (hg _ (by decide)).trans M.s2, (hg _ (by decide)).trans M.s3, (hg _ (by decide)).trans M.s4,
    (hg _ (by decide)).trans M.s5, (hg _ (by decide)).trans M.s6,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      simp only [oSave, oRa] at this hd
      exact Offset.disjoint _ (by omega_using [hd, this]) (by unfold frameBytes at hd'; omega_using [this])
        (by unfold frameBytes at hd'; omega_using [hd'])⟩
  rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')

/-- At the call of `vg_rsa_public_precompute`. -/
structure AtPre (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  a0 : u.gpr .a0 = fb s + BitVec.ofNat 64 oPre
  a1 : u.gpr .a1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)
  a2 : u.gpr .a2 = s.gpr .a2
  a3 : u.gpr .a3 = s.gpr .a3
  a4 : u.gpr .a4 = stackArg s 10
  a5 : u.gpr .a5 = stackArg s 11

theorem preLen_val {x : BitVec 64} (hk : x.toNat ≤ 1024) :
    (x + BitVec.ofNat 64 7) >>> 3 <<< 1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Spec.Rsa.precomputedWords, Spec.Rsa.modulusWords]
  omega_using [hk]

/-- `preArgs` up to `argBase`. -/
abbrev pre1 : List Instr :=
  [.addSp .t0 0, .store .d .a0 .t0 oSt, .addi .a0 .t0 oPre] ++ preLen .a1 ++ [mov .a2 .s2, mov .a3 .s3]

theorem preArgs_eq : preArgs = pre1 ++ (argBase ++ ([.load .d .a4 .t6 80, .load .d .a5 .t6 88] : List Instr)) := by
  simp only [preArgs, List.append_assoc]

theorem pre1_ok {s t : State} (h : PreP pc s) (M : Mid s t) :
    WP isa (.block pre1) t fun w =>
      (w.gpr .a0 = fb s + BitVec.ofNat 64 oPre ∧
        w.gpr .a1 = BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) ∧
        w.gpr .a2 = s.gpr .a2 ∧ w.gpr .a3 = s.gpr .a3 ∧
        w.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .a0)) ∧
      Keep [.t0, .a0, .a1, .a2, .a3] t w := by
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 152) 8 := by
    rw [M.wr]; exact in_fr s _ (by decide)
  have hal : (fb s + BitVec.ofNat 64 152).toNat % 8 = 0 := fb_al8 h (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [pre1, exec_addSp, M.sp, BitVec.add_zero, ho, hal, oSt, oPre, preLen, mov, M.s2, M.s3, preLen_val h.k2]

theorem pre2_ok {s x : State} (h : PreP pc s) (hrd : x.rd = s.rd) (hm : Frame [kR s, sR s] s.mem x.mem)
    (h6 : x.gpr .t6 = s.sp) :
    WP isa (.block [.load .d .a4 .t6 80, .load .d .a5 .t6 88]) x fun u =>
      (u.gpr .a4 = stackArg s 10 ∧ u.gpr .a5 = stackArg s 11 ∧ u.mem = x.mem) ∧ Keep [.a4, .a5] x u := by
  have i0 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 80) 8 := arg_in h hrd (j := 10) (by decide)
  have i1 : InRegions (x.rd ++ x.wr) (s.sp + BitVec.ofNat 64 88) 8 := arg_in h hrd (j := 11) (by decide)
  have l0 : (s.sp + BitVec.ofNat 64 80).toNat % 8 = 0 := stackArgAddr_al h 10
  have l1 : (s.sp + BitVec.ofNat 64 88).toNat % 8 = 0 := stackArgAddr_al h 11
  have r0 : x.mem.readW (s.sp + BitVec.ofNat 64 80) 64 = stackArg s 10 := arg_read2 h hm (j := 10) (by decide)
  have r1 : x.mem.readW (s.sp + BitVec.ofNat 64 88) 64 = stackArg s 11 := arg_read2 h hm (j := 11) (by decide)
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [h6, i0, i1, l0, l1, r0, r1]

theorem preArgs_ok {s t : State} (h : PreP pc s) (M : Mid s t) (C : crtOut s t) :
    WP isa (.block preArgs) t (AtPre s) := by
  have hk := h.k2
  rw [preArgs_eq, WP.block_append_iff]
  refine WP.mono (WP.rdwr (pre1_ok h M)) fun w ⟨⟨⟨w0, w1, w2, w3, wm⟩, kw⟩, wrd, wwr, wsp⟩ => ?_
  refine argBase_ok (s := s) (wsp.trans M.sp) fun x x6 kx xm xsp => ?_
  have hmw : Frame [kR s, sR s] s.mem x.mem := by
    rw [xm, wm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s (by decide))
  refine WP.mono (WP.rdwr (pre2_ok h (kx.2.1.trans (wrd.trans M.rd)) hmw x6))
    fun u ⟨⟨⟨u4, u5, um⟩, ku⟩, urd, uwr, usp⟩ => ?_
  have hum : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oSt) (t.gpr .a0) := by rw [um, xm, wm]
  refine ⟨M.store (d := oSt) (.inl (by decide)) (by decide) _ (fun r hr => ?_) (usp.trans (xsp.trans wsp))
    (urd.trans (kx.2.1.trans wrd)) (uwr.trans (kx.2.2.trans wwr)) hum, ?_, ?_, ?_, ?_, ?_, u4, u5⟩
  · rw [ku.gpr (by revert r; decide), kx.gpr (by revert r; decide), kw.gpr (by revert r; decide)]
  · have hb : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat := by
      simp only [Spec.Rsa.bytesAt]
      refine List.map_congr_left fun i hi => ?_
      have hi := List.mem_range.mp hi
      rw [hum]
      exact Frame.bytes (R := mR s) (Frame.writeW (Frame.refl [⟨fb s + BitVec.ofNat 64 oSt, 8⟩] t.mem)
        (List.mem_singleton_self _) _ (Region.contains_self _ _))
        (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact Offset.disjoint _ (.inr (by decide)) (by unfold oM; omega_using [hk]) (by decide))
        (show (s.gpr .a3).toNat ≤ 2 ^ 64 by omega_using []) hi
    show Spec.Rsa.written _ _ _ _ _
    rw [hum, Mem.readW_writeW_self64, ← hum]
    exact written_congr hb C
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w0
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w1
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w2
  · rw [ku.gpr (by decide), kx.gpr (by decide)]; exact w3

/-- `n`'s values, in the frame. -/
abbrev pwR (s : State) : Region :=
  ⟨fb s + BitVec.ofNat 64 oPre, Spec.Rsa.precomputedWords (s.gpr .a3).toNat * 8⟩

/-- The regions the call writes. -/
abbrev preWr (s : State) : List Region := [pwR s, sR s]

theorem pw_le {k : Nat} (hk : k ≤ 1024) : Spec.Rsa.precomputedWords k ≤ 256 := by
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords; omega_using [hk]

theorem pwR_sub {s : State} (h : PreP pc s) : Region.Sub (pwR s) (kR s) :=
  frame_sub s (by have := pw_le h.k2; unfold oPre frameBytes; omega_using [this])

/-- The frame below `n`'s values is apart from what the call writes. -/
theorem below_pre {s : State} (h : PreP pc s) {d n : Nat} (hd : d + n ≤ oPre) {r : Region} (hr : r ∈ preWr s) :
    Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint _ (.inl hd) (by unfold oPre at hd; omega_using [hd])
      (by have := pw_le h.k2; unfold oPre; omega_using [this])
  · exact h.ks.sub_left (frame_sub s (by unfold oPre frameBytes at *; omega_using [hd]))

/-- `n`'s values: computed (`publicPrecompute`, or zeros if they are
invalid), or, with `pc`, the first words of `pre`. -/
abbrev preVal (pc : Bool) (s : State) : List (BitVec 64) :=
  if pc then Spec.Rsa.wordsAt s.mem (stackArg s 12) (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)
  else (Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)).getD
    (List.replicate (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) 0)

/-- `n`'s values in the frame. -/
abbrev preW (pc : Bool) (s : State) (m : Mem) : Prop :=
  Spec.Rsa.wordsAt m (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) = preVal pc s

theorem preW_of {s : State} {r : BitVec 64} {m : Mem}
    (h : Proof.Bignum.RISCV64.Pre.preOut (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
      (fb s + BitVec.ofNat 64 oPre) (Spec.Rsa.precomputedWords (s.gpr .a3).toNat) r m) : preW false s m := by
  simp only [preW, preVal, Bool.false_eq_true, ↓reduceIte]
  cases hw : Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) <;>
    simp only [Proof.Bignum.RISCV64.Pre.preOut, hw] at h <;> exact h.2

/-- After `n`'s values. -/
structure AtPub (pc : Bool) (s u : State) : Prop extends Mid s u where
  crt : crtOutM s u
  pre : preW pc s u.mem

theorem pre_noFrames : Impl.Bignum.RISCV64.Precompute.precompute.noFrames = true := by decide +kernel

theorem pre_covers {s t : State} (h : PreP pc s) (A : AtPre s t) :
    Covers ([nR s] ++ preWr s) (t.rd ++ t.wr) ∧ Covers (preWr s) t.wr := by
  have hk := h.k2
  have pwl := pw_le hk
  have hw : Covers (preWr s) t.wr := by
    rw [A.wr, h.hwr]
    refine Covers.of_forall fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Covers.one (in_fr s _ (by unfold oPre frameBytes; omega_using [pwl]))
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; simp
  refine ⟨Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.right hw), hw⟩
  rw [List.mem_singleton.mp hr, A.rd, h.hrd]; simp

theorem pre_toNat {s : State} (h : PreP pc s) :
    (BitVec.ofNat 64 (Spec.Rsa.precomputedWords (s.gpr .a3).toNat)).toNat =
      Spec.Rsa.precomputedWords (s.gpr .a3).toNat := by
  have := pw_le h.k2
  rw [BitVec.toNat_ofNat]; omega_using [this]

theorem pre_pre {s t : State} (h : PreP pc s) (A : AtPre s t) :
    Proof.Bignum.RISCV64.Pre.fnContract.pre (t.callEntry.withRegions [nR s] (preWr s)) := by
  have hk := h.k2
  have pk := pwR_sub h
  have pwl := pw_le hk
  have fbt := fb_toNat h.sp1
  unfold frameBytes at fbt
  have g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  simp only [Proof.Bignum.RISCV64.Pre.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
    g .a3 (by decide), g .a4 (by decide), g .a5 (by decide), A.a0, A.a1, A.a2, A.a3, A.a4, A.a5, pre_toNat h,
    State.withRegions_rd, State.withRegions_wr, Proof.Bignum.RISCV64.Pre.nR, Proof.Bignum.RISCV64.Pre.preR,
    Proof.Bignum.RISCV64.Pre.scrR]
  refine ⟨trivial, trivial, h.kn.sub_left pk, h.ks.sub_left pk, h.ns, ?_, h.wn, h.ws, ⟨h.k1, h.k2⟩, trivial, ?_,
    fb_al8 h (by decide), h.al⟩
  · rw [Offset.toNat_add_ofNat]; unfold oPre at *; omega_using [pwl, fbt]
  · have := h.hs; have := h.k1; unfold Spec.Rsa.scratchWords at *
    unfold Spec.Rsa.publicScratchWords Spec.Rsa.modulusWords; omega_arith

theorem preCall_ok {s t : State} (h : PreP pc s) (A : AtPre s t) {Q : State → Prop}
    (hQ : ∀ u, AtPub false s u → Q u) : WP isa preCall t Q := by
  have hk := h.k2
  have pk := pwR_sub h
  obtain ⟨hc, hw⟩ := pre_covers h A
  have g : ∀ r, r ∉ linkRegs → (t.callEntry.withRegions [nR s] (preWr s)).gpr r = t.gpr r :=
    fun r hr => State.callEntry_gpr t hr
  have e4 := pre_toNat h
  have hn : Spec.Rsa.bytesAt t.mem (s.gpr .a2) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat :=
    bytes_of_frame A.mem (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.kn.symm
      · exact h.ns) (by have := h.wn; omega_using [])
  unfold preCall
  refine WP.call (k := Proof.Bignum.RISCV64.Pre.fnContract) (rd := [nR s]) (wr := preWr s)
    Proof.Bignum.RISCV64.Pre.fn_correct (pre_pre h A) hc hw
    (fun u hrd hwr hsp hf hpres _ hpost => hQ u ?_) pre_noFrames
  have hp : ∀ r ∈ preserved, u.gpr r = t.gpr r := hpres
  have ft : Frame [kR s, sR s] s.mem u.mem := by
    refine (A.mem.trans (hf.sub fun r hr => ?_))
    simp only [preWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., pk⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), fun _ h => h⟩
  have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .a3).toNat :=
    bytes_of_frame (s := t) hf (fun r hr => below_pre h (by unfold oM oPre; omega_using [hk]) hr) (by omega_using [])
  have hst : u.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 = t.mem.readW (fb s + BitVec.ofNat 64 oSt) 64 :=
    hf.readW (Region.contains_self _ _) (fun r hr => below_pre h (by decide) hr) (by decide)
  refine ⟨⟨hsp.trans A.sp, hrd.trans A.rd, hwr.trans A.wr, (hp _ (by decide)).trans A.s1,
    (hp _ (by decide)).trans A.s2, (hp _ (by decide)).trans A.s3, (hp _ (by decide)).trans A.s4,
    (hp _ (by decide)).trans A.s5, (hp _ (by decide)).trans A.s6,
    fun r hr => (hp r (by revert r; decide)).trans (A.hi r hr), ft, A.sv.frame hf fun p hp' r hr => below_pre h (by
      have := saved_offs p hp'; unfold oSave oPre at *; omega_using [this]) hr⟩, ?_, ?_⟩
  · show Spec.Rsa.written _ _ _ _ _
    rw [hst]; exact written_congr hm A.crt
  · simp only [Proof.Bignum.RISCV64.Pre.fnContract, g .a0 (by decide), g .a1 (by decide), g .a2 (by decide),
      g .a3 (by decide), A.a0, A.a1, A.a2, A.a3, e4, State.withRegions_mem, State.withRegions_gpr,
      State.callEntry_mem, hn] at hpost
    exact preW_of hpost

end VG.Proof.Rsa.RISCV64.Priv
