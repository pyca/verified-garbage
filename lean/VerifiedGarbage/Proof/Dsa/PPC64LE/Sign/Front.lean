module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFront
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Bignum.FrameOutside
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run

/-!
# DSA signing on PPC64LE: the contract on the registers, and the entry

`sContract`: `vg_dsa_sign(out = r3, out_len = r4, key = r5, key_len = r6,
p_len = r7, nonce = r8, q_len = r9, digest = r10, digest_len, scratch,
scratch_len)`, the last three on the stack. `sfront_ok`: `entry` loads
`scratch`'s address from the stack, saves the nonvolatile registers in its
header, keeps `out` in its word `hOut`, and the other arguments and the
lengths in registers (`Regs`, `r2`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG.Impl.Dsa.PPC64LE.Sign (hOut)
open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The arguments on the stack: `digest_len`, `scratch` and `scratch_len`. -/
abbrev sStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The signature `signBytes` gives, on entry. -/
def sRes (s : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (s.gpr .r7).toNat (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat)

/-- `vg_dsa_sign`, on the registers and the stack. -/
def sContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let key : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let nc : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let dg : Region := ⟨s.gpr .r10, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 11 ≤ 2 ^ 64 ∧ s.rd = [key, nc, dg, sStackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint key ∧ out.Disjoint nc ∧ out.Disjoint dg ∧ out.Disjoint scr ∧ out.Disjoint (sStackArgs s) ∧
      key.Disjoint scr ∧ nc.Disjoint scr ∧ dg.Disjoint scr ∧ scr.Disjoint (sStackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r7).toNat (s.gpr .r9).toNat ∧
      (s.gpr .r4).toNat = 2 * (s.gpr .r9).toNat ∧
      (s.gpr .r6).toNat = 3 * (s.gpr .r7).toNat + 2 * (s.gpr .r9).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .r7).toNat ≤ (stackArg s 2).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = Spec.Dsa.signStatus (sRes s) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat = (sRes s).getD (List.replicate (s.gpr .r4).toNat 0)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .r7).toNat (s₁.gpr .r9).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat) ++ [Spec.Dsa.signStatus (sRes s₁)] =
      Spec.Dsa.publicBytesLeak (s₂.gpr .r7).toNat (s₂.gpr .r9).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat) ++ [Spec.Dsa.signStatus (sRes s₂)]

/-- A call's layout. -/
def slayOf (s : State) : Lay := ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .r7).toNat, (s.gpr .r9).toNat⟩

theorem slayOf_ok {s : State} (h : sContract.pre s) : (slayOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [slayOf]; omega_arith, by simp only [slayOf]; omega_arith, by simp only [slayOf]; omega_arith, nw⟩

/-- A run keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun t => Q t ∧ t.sp = s.sp :=
  let ⟨tr, t, e, q⟩ := h
  ⟨tr, t, e, q, Exec.sp e⟩

/-- The working space's address, the stack's second argument, into `r11`. -/
theorem sloadS_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8) :
    WP isa (.block [.addSp .r11 104, .load .d .r11 .r11 0]) s fun t =>
      (t.gpr .r11 = stackArg s 1 ∧ t.mem = s.mem) ∧ Keep [.r11] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r11 104) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 104)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- The stack's arguments lie apart from the header's word `hOut`. -/
theorem stack_sep {S B : Addr} {Z : Nat} (hd : (⟨S, Z⟩ : Region).Disjoint ⟨B, 24⟩) (hZ : 16 ≤ Z) :
    Mem.Sep B 8 (S + BitVec.ofNat 64 hOut) 8 := by
  intro x h₁ h₂
  rw [hOut, Offset.lt_iff x S (by decide)] at h₂
  exact hd x (by simp only [Region.Contains]; omega_arith) (by simp only [Region.Contains]; omega_arith)

/-- The stack's arguments are kept by a change in the header. -/
theorem stack_kept {S B : Addr} {Z : Nat} (hd : (⟨S, Z⟩ : Region).Disjoint ⟨B, 24⟩) (hZ : 256 ≤ Z)
    {m m' : Mem} (ho : Outside S 0 256 m m') : m'.readW B 64 = m.readW B 64 := by
  refine Mem.readW_congr fun i hi => ho _ (Or.inr ?_)
  by_contra hc
  have hlt := (B + BitVec.ofNat 64 i - S).isLt
  exact hd (B + BitVec.ofNat 64 i) (by simp only [Region.Contains, ofs] at hc ⊢; omega_arith)
    (by simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat B (by omega_arith)]; omega_arith)

/-- After the registers are saved: the key, the nonce and the digest into
`r27`, `r28` and `r26`, `out` into `hOut`, `digest_len` into `r10`, and the
lengths into `r2`. -/
theorem stail_ok {s : State} {S : Addr} (h21 : s.gpr .r21 = S)
    (hst : InRegions s.wr (S + BitVec.ofNat 64 hOut) 8) (hld : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 96) 8)
    (hsep : Mem.Sep (s.sp + BitVec.ofNat 64 96) 8 (S + BitVec.ofNat 64 hOut) 8)
    (h7 : (s.gpr .r7).toNat < 2 ^ 16) (h9 : (s.gpr .r9).toNat < 2 ^ 16) :
    WP isa (.block (([.addi .r27 .r5 0, .addi .r28 .r8 0, .addi .r26 .r10 0, .store .d .r3 .r21 hOut,
      .addSp .r10 96, .load .d .r10 .r10 0] : List Instr) ++ (Verify.capD ++
      ([.lsl .r4 .r4 48, .lsl .r0 .r9 16, .add .r2 .r7 .r0, .add .r2 .r2 .r4] : List Instr)))) s fun t =>
      (t.gpr .r27 = s.gpr .r5 ∧ t.gpr .r28 = s.gpr .r8 ∧ t.gpr .r26 = s.gpr .r10 ∧
        t.gpr .r2 = pack (s.gpr .r7).toNat (s.gpr .r9).toNat 0
          (min (s.mem.readW (s.sp + BitVec.ofNat 64 96) 64).toNat 64) ∧
        t.mem = s.mem.writeW (S + BitVec.ofNat 64 hOut) (s.gpr .r3)) ∧
        Keep [.r27, .r28, .r26, .r10, .r0, .r4, .r2] s t := by
  refine WP.block_append (WP.mono (WP.keep [.r27, .r28, .r26, .r10] (Q := fun u => u.gpr .r27 = s.gpr .r5 ∧
      u.gpr .r28 = s.gpr .r8 ∧ u.gpr .r26 = s.gpr .r10 ∧
      u.gpr .r10 = s.mem.readW (s.sp + BitVec.ofNat 64 96) 64 ∧
      u.mem = s.mem.writeW (S + BitVec.ofNat 64 hOut) (s.gpr .r3)) ?_ (by decide))
    fun u ⟨⟨a27, a28, a26, a10, mu⟩, ku⟩ => ?_)
  · have es : exec (.store .d .r3 .r21 hOut)
        (((s.write .r27 (s.gpr .r5)).write .r28 (s.gpr .r8)).write .r26 (s.gpr .r10)) =
        some { ((s.write .r27 (s.gpr .r5)).write .r28 (s.gpr .r8)).write .r26 (s.gpr .r10) with
          mem := s.mem.writeW (S + BitVec.ofNat 64 hOut) (s.gpr .r3) } := by
      subst h21
      exact exec_std (by decide) hst
    have ea : ∀ v : State, exec (.addSp .r10 96) v = some (v.write .r10 (v.sp + BitVec.ofNat 64 96)) := by
      intro v; simp [exec]
    have hv : (s.mem.writeW (S + BitVec.ofNat 64 hOut) (s.gpr .r3)).readW (s.sp + BitVec.ofNat 64 96) 64 =
        s.mem.readW (s.sp + BitVec.ofNat 64 96) 64 := Mem.readW_writeW_sep hsep (by decide)
    prun [BitVec.add_zero, es, ea, hld, hv]
  refine WP.block_append (WP.mono (capD_ok u) fun v ⟨⟨b4, mv⟩, kv⟩ => ?_)
  rw [a10] at b4
  have hd : min (s.mem.readW (s.sp + BitVec.ofNat 64 96) 64).toNat 64 < 2 ^ 16 := by omega_arith
  have v7 : v.gpr .r7 = s.gpr .r7 := (kv.gpr .r7 (by decide)).trans (ku.gpr .r7 (by decide))
  have v9 : v.gpr .r9 = s.gpr .r9 := (kv.gpr .r9 (by decide)).trans (ku.gpr .r9 (by decide))
  refine WP.mono (WP.keep [.r4, .r0, .r2] (Q := fun w =>
      w.gpr .r2 = pack (s.gpr .r7).toNat (s.gpr .r9).toNat 0
        (min (s.mem.readW (s.sp + BitVec.ofNat 64 96) 64).toNat 64) ∧ w.mem = v.mem)
    (by prun [b4, v7, v9, pack_entry _ _ h7 h9 hd]) (by decide))
    fun w ⟨⟨c2, mw⟩, kw⟩ => ⟨⟨(kw.gpr .r27 (by decide)).trans ((kv.gpr .r27 (by decide)).trans a27),
      (kw.gpr .r28 (by decide)).trans ((kv.gpr .r28 (by decide)).trans a28),
      (kw.gpr .r26 (by decide)).trans ((kv.gpr .r26 (by decide)).trans a26), c2, mw.trans (mv.trans mu)⟩,
      ((ku.trans kv).trans kw).mono (by decide)⟩

/-- The registers `Sign.entry` writes. -/
def sEntryRegs : List Reg := [.r0, .r2, .r4, .r10, .r11, .r21, .r26, .r27, .r28]

/-- `Sign.entry`: `scratch` (from the stack) into `r21`, the nonvolatile
registers saved in its header, `out` in its word `hOut`, and the other
arguments and the lengths in registers (`Regs`, `r2`). Memory changes only in
the header. -/
theorem sfront_ok {s : State} (h : sContract.pre s) :
    WP isa (.block Sign.entry) s fun t =>
      (Regs t (slayOf s) (s.gpr .r5) (s.gpr .r8) (s.gpr .r10) ∧ ScrL t (slayOf s) ∧
        t.gpr .r2 = pack (slayOf s).pl (slayOf s).ql 0 (min (stackArg s 0).toNat 64) ∧
        word t.mem (stackArg s 1) hOut = s.gpr .r3 ∧
        (∀ i < 19, word t.mem (stackArg s 1) (saveOff i) = s.gpr (saved i)) ∧
        Outside (stackArg s 1) 0 256 s.mem t.mem) ∧ Keep sEntryRegs s t := by
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hpl : (s.gpr .r7).toNat < 2 ^ 16 := by have := hL.pl; simp only [slayOf] at this; omega_arith
  have hql : (s.gpr .r9).toNat < 2 ^ 16 := by have := hL.ql; simp only [slayOf] at this; omega_arith
  obtain ⟨-, hrd, hwr, -, -, -, -, -, -, -, -, dST, -, -, -, -, nw, -, -, -, -⟩ := h
  have hZ' : 256 ≤ (stackArg s 2).toNat * 8 := hZ
  have hstk : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8 :=
    ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by simp [Region.Contains]⟩
  have e1 : stackArgAddr s 1 = stackArgAddr s 0 + BitVec.ofNat 64 8 := by
    simp only [stackArgAddr]; rw [Offset.add_add]
  have hstk1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 :=
    ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
      simp only [Region.Contains]; rw [e1, Mem.sub_ofNat_toNat _ (by decide)]; decide⟩
  unfold Sign.entry
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (wp_sp (sloadS_ok s hstk1)) fun s₁ ⟨⟨⟨a11, m1⟩, k1⟩, sp1⟩ => ?_)
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (slayOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [slayOf]) nw
  have hin : ∀ i < 19, InRegions s₁.wr (off (savW (s₁.gpr .r11)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq, a11]
    exact (hscr s₁ k1.wr).st (d := 104 + 8 * i) (by simp only [slayOf] at hZ ⊢; omega_arith)
  refine WP.block_append (WP.mono (wp_sp (save_ok s₁ hin)) fun s₂ ⟨hS, sp2⟩ => ?_)
  have k12 := k1.trans hS.keep
  have h21 : s₂.gpr .r21 = stackArg s 1 := hS.r21.trans a11
  have e : ∀ r, r ≠ .r11 → r ≠ .r21 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr r fun hm => by
      simp only [List.mem_append, List.mem_singleton] at hm
      exact hm.elim h1 h2
  have f2 : Outside (stackArg s 1) 104 152 s₁.mem s₂.mem :=
    VG.Proof.Bignum.frame_outside (by rw [← a11]; exact hS.frame) (by decide)
  have o2 : Outside (stackArg s 1) 0 256 s.mem s₂.mem := by
    rw [← m1]; exact f2.mono (Nat.zero_le _) (by decide)
  have hsp : s₂.sp = s.sp := sp2.trans sp1
  have hd : s₂.mem.readW (s₂.sp + BitVec.ofNat 64 96) 64 = stackArg s 0 := by
    rw [hsp]; exact stack_kept (B := stackArgAddr s 0) dST hZ' o2
  refine WP.mono (stail_ok h21 ((hscr s₂ k12.wr).st (d := hOut) (by simp only [hOut, slayOf] at hZ ⊢; omega_arith))
    (by rw [hsp, k12.rd, k12.wr]; exact hstk)
    (by rw [hsp]; exact stack_sep (B := stackArgAddr s 0) dST (by omega_arith)) (by rw [e _ (by decide) (by decide)]; exact hpl) (by rw [e _ (by decide) (by decide)]; exact hql))
    fun t ⟨⟨t27, t28, t26, t2, mt⟩, kt⟩ => ?_
  have k := k12.trans kt
  rw [e .r5 (by decide) (by decide)] at t27
  rw [e .r8 (by decide) (by decide)] at t28
  rw [e .r10 (by decide) (by decide)] at t26
  rw [e .r7 (by decide) (by decide), e .r9 (by decide) (by decide), hd] at t2
  rw [e .r3 (by decide) (by decide)] at mt
  have t21 : t.gpr .r21 = stackArg s 1 := (kt.gpr .r21 (by decide)).trans h21
  have wo : Outside (stackArg s 1) hOut 8 s₂.mem t.mem := by
    rw [mt]; exact writeW_outside s₂.mem _ _ (by decide)
  refine ⟨⟨Regs.of_pack hL t21 t27 t28 t26 t2 (by decide) (by omega_arith), hscr t k.wr, t2,
    by rw [mt]; exact word_writeW_self _ _ _ _, fun i hi => ?_, ?_⟩, k.mono (by decide)⟩
  · rw [Outside.word wo (Or.inr (by simp only [hOut, saveOff]; omega_arith)) (by simp only [saveOff]; omega_arith)]
    show s₂.mem.readW (stackArg s 1 + BitVec.ofNat 64 (104 + 8 * i)) 64 = _
    rw [saveOff_eq, ← a11, hS.saved i hi]
    exact k1.gpr _ fun h => front_saved_ne11 i hi (List.mem_singleton.mp h)
  · exact o2.trans (wo.mono (Nat.zero_le _) (by decide))

end VG.Proof.Dsa.PPC64LE
